"""
IPTV - atualizador automatico de playlists.

Uso:
    py install_iptv.py            # configura tudo (git, agendador) e roda a atualizacao
    py install_iptv.py --run      # so atualiza (usado pelo Agendador de Tarefas)
    py install_iptv.py --force    # reprocessa mesmo sem mudanca nas fontes
    py install_iptv.py --hora 05:30   # muda o horario da tarefa diaria

Fluxo: baixa as fontes (so se mudaram, via ETag + hash) -> remove repeticoes ->
divide em arquivos menores por categoria -> commit + push no GitHub.
"""

import argparse
import hashlib
import json
import logging
import re
import shutil
import subprocess
import sys
import time
import unicodedata
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.parse import urlsplit

# ---------------------------------------------------------------- configuracao

# Ordem = prioridade: quando um titulo se repete, fica a versao da primeira fonte.
SOURCES = [
    "https://raw.githubusercontent.com/Ramys/Iptv-Brasil-2026/refs/heads/master/CanaisBR01.m3u8",
    "https://raw.githubusercontent.com/Ramys/Iptv-Brasil-2026/refs/heads/master/CanaisBR02.m3u8",
    "https://raw.githubusercontent.com/Ramys/Iptv-Brasil-2026/refs/heads/master/CanaisBR03.m3u8",
    "https://raw.githubusercontent.com/Ramys/Iptv-Brasil-2026/refs/heads/master/CanaisBR04.m3u8",
    "https://raw.githubusercontent.com/Ramys/Iptv-Brasil-2026/refs/heads/master/Filmes-Series.m3u8",
]

# usuario na URL faz o Git Credential Manager usar a conta certa
REPO_URL = "https://iptvbrazil2030@github.com/iptvbrazil2030/iptv.git"
# identidade dos commits (so neste repositorio, nao altera o git global)
GIT_NAME = "iptvbrazil2030"
GIT_EMAIL = "339355163+iptvbrazil2030@users.noreply.github.com"
BRANCH = "main"
RAW_BASE = "https://raw.githubusercontent.com/iptvbrazil2030/iptv/main"
PAGES_BASE = "https://iptvbrazil2030.github.io/iptv"
TASK_NAME = "IPTV Atualizar"
DEFAULT_HOUR = "04:00"

# Tamanho maximo de cada arquivo gerado (GitHub bloqueia > 100 MB e avisa > 50 MB;
# arquivos menores tambem carregam bem mais rapido no Kodi).
MAX_FILE_BYTES = 20 * 1024 * 1024

# Conjuntos gerados: "" = principal (raiz do repo), "reserva" = mesmos titulos usando
# o link de outro servidor. Para ter mais um nivel, adicione "reserva2".
MIRRORS = ["", "reserva"]

# Conteudo adulto (canais e filmes): False = removido de todas as listas
INCLUDE_ADULT = False

# Teste de saude: a cada execucao testa HEALTH_SAMPLES links de cada fonte.
# Fonte com menos de HEALTH_MIN funcionando e ignorada (conta expirada/servidor fora).
HEALTH_SAMPLES = 8
HEALTH_MIN = 0.3
HEALTH_TIMEOUT = 10

ROOT = Path(__file__).resolve().parent
CACHE = ROOT / ".cache"
LOGS = ROOT / "logs"
STATE_FILE = CACHE / "state.json"

# Arquivos/pastas gerados (apagados e recriados a cada processamento)
LEGACY_M3U8 = ["playlist", "filmes"]
OUT_DIRS = ["series", "filmes", "outros"]

log = logging.getLogger("iptv")


def setup_logging():
    LOGS.mkdir(exist_ok=True)
    handlers = [logging.FileHandler(LOGS / "iptv.log", encoding="utf-8")]
    if sys.stdout is not None:  # pythonw nao tem console
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass
        handlers.append(logging.StreamHandler(sys.stdout))
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s",
                        datefmt="%Y-%m-%d %H:%M:%S", handlers=handlers)


# ---------------------------------------------------------------- download

def load_state():
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_state(state):
    CACHE.mkdir(exist_ok=True)
    STATE_FILE.write_text(json.dumps(state, indent=2), encoding="utf-8")


def cache_path(url):
    return CACHE / url.rsplit("/", 1)[-1]


def download(url, state):
    """Baixa a fonte se mudou. Retorna True se o conteudo mudou."""
    path = cache_path(url)
    info = state.get(url, {})
    headers = {"User-Agent": "Mozilla/5.0 iptv-updater"}
    if path.exists() and info.get("etag"):
        headers["If-None-Match"] = info["etag"]

    for attempt in range(1, 4):
        try:
            req = urllib.request.Request(url, headers=headers)
            tmp = path.with_suffix(".part")
            sha = hashlib.sha256()
            with urllib.request.urlopen(req, timeout=60) as resp, open(tmp, "wb") as fh:
                while chunk := resp.read(1024 * 1024):
                    sha.update(chunk)
                    fh.write(chunk)
                etag = resp.headers.get("ETag")
            digest = sha.hexdigest()
            changed = digest != info.get("sha256")
            tmp.replace(path)
            state[url] = {"etag": etag, "sha256": digest}
            log.info("  %s: %s (%.1f MB)", path.name, "ATUALIZADO" if changed else "igual",
                     path.stat().st_size / 1e6)
            return changed
        except urllib.error.HTTPError as e:
            if e.code == 304:
                log.info("  %s: sem mudanca", path.name)
                return False
            log.warning("  %s: HTTP %s (tentativa %d)", path.name, e.code, attempt)
        except Exception as e:
            log.warning("  %s: erro %s (tentativa %d)", path.name, e, attempt)
        time.sleep(5 * attempt)

    if path.exists():
        log.warning("  %s: falhou, usando copia em cache", path.name)
    else:
        log.error("  %s: falhou e nao ha cache, fonte ignorada", path.name)
    return False


# ---------------------------------------------------------------- parse / processamento

ATTR_RE = re.compile(r'([\w-]+)="([^"]*)"')


def strip_accents(s):
    return "".join(c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c))


# Grupos com nomes diferentes entre as fontes que sao a mesma coisa
GROUP_ALIASES = {
    "NOVELAS": "SERIES | NOVELAS",
    "SERIES | AMAZON PRIME": "SERIES | AMAZON PRIME VIDEO",
    "SERIES | APPLE PLUS": "SERIES | APPLE TV PLUS",
    "SERIES | CRUNCHOROLL": "SERIES | CRUNCHYROLL",
    "SERIES | DISCOVERY +": "SERIES | DISCOVERY PLUS",
    "SERIES | DISNEY +": "SERIES | DISNEY PLUS",
    "SERIES | DORAMAS": "SERIES | DORAMA",
    "SERIES | LIONSGASTE": "SERIES | LIONSGATE",
    "SERIES | MAX M": "SERIES | MAX",
    "SERIES | PLUTOTV": "SERIES | PLUTO TV",
    "FILMES | 4K UHD": "FILMES | 4K",
    "CINEMA": "FILMES | CINEMA",
}


def norm_group(g):
    """'SÉRIES / NETFLIX ⚡' e 'Series | Netflix' -> 'SERIES | NETFLIX'."""
    g = strip_accents(g).upper().replace("/", "|").replace(":", "|")
    g = re.sub(r"[^\w\s|&+\-\[\]]", " ", g)
    parts = [re.sub(r"\s+", " ", p).strip() for p in g.split("|")]
    g = " | ".join(p for p in parts if p) or "SEM GRUPO"
    return GROUP_ALIASES.get(g, g)


def norm_title(t):
    return re.sub(r"\s+", " ", t).strip().casefold()


# Canais adultos conhecidos que podem aparecer fora de um grupo "adultos"
ADULT_CHANNEL_RE = re.compile(
    r"\b(playboy tv|sexy ?hot|venus|private|brazzers|hustler|dorcel|penthouse|redlight|"
    r"sextreme|for ?man|xxx)\b", re.I)


def classify(url, group, title=""):
    u = url.lower().split("?")[0]
    if re.search(r"xxx|adult|\+18|18\+", group, re.I):
        return "adultos"
    is_live = u.endswith((".ts", ".m3u8")) or not re.search(r"\.\w{2,4}$", u)
    if is_live and "/movie/" not in u and "/series/" not in u and ADULT_CHANNEL_RE.search(title):
        return "adultos"
    if "/series/" in u:
        return "series"
    if "/movie/" in u:
        return "filmes"
    if u.endswith((".ts", ".m3u8")) or not re.search(r"\.\w{2,4}$", u):
        return "canais"
    if re.search(r"SERIE|NOVELA|DORAMA|ANIME|DESENHO", group):
        return "series"
    if re.search(r"FILME|CINEMA", group):
        return "filmes"
    return "outros"


def parse_m3u(path):
    """Gera (titulo, atributos, url) de cada entrada."""
    extinf = None
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            if line.startswith("#EXTINF"):
                extinf = line
            elif not line.startswith("#") and extinf:
                q = extinf.rfind('"')
                comma = extinf.find(",", q if q != -1 else 0)
                title = extinf[comma + 1:].strip() if comma != -1 else ""
                attrs = dict(ATTR_RE.findall(extinf[:comma] if comma != -1 else extinf))
                yield title or attrs.get("tvg-name", ""), attrs, line
                extinf = None


def extinf_line(title, attrs, group, kind):
    parts = ["#EXTINF:-1"]
    keys = ["tvg-id", "tvg-name", "tvg-logo"] if kind == "canais" else ["tvg-logo"]
    for k in keys:
        if attrs.get(k):
            parts.append(f'{k}="{attrs[k]}"')
    parts.append(f'group-title="{group}"')
    if kind != "canais":
        # IPTV Simple (Kodi 20+) mostra entradas media="true" como VOD em "Gravacoes",
        # em pastas por media-dir e agrupando episodios SxxEyy por serie/temporada
        parts.append('media="true"')
        parts.append(f'media-dir="/{group.replace(" | ", "/")}"')
    return " ".join(parts) + "," + title


def sample_links(path, n):
    """Pega n links espalhados pelo arquivo (canais e VOD)."""
    links = [l for _, _, l in parse_m3u(path)]
    if not links:
        return []
    step = max(1, len(links) // n)
    return links[::step][:n]


def is_video(head):
    """Confere a assinatura dos primeiros bytes: alguns servidores mortos respondem
    206 video/mp4 com uma pagina HTML no corpo."""
    return (head[:1] == b"\x47"                                   # MPEG-TS
            or head[4:8] in (b"ftyp", b"moov", b"mdat", b"free")  # MP4
            or head[:4] == b"\x1a\x45\xdf\xa3"                    # MKV
            or head[:4] == b"RIFF"                                # AVI
            or head[:7] == b"#EXTM3U")                            # HLS


def link_ok(link):
    req = urllib.request.Request(link, headers={"User-Agent": "VLC/3.0.20 LibVLC/3.0.20",
                                                "Range": "bytes=0-1023"})
    try:
        with urllib.request.urlopen(req, timeout=HEALTH_TIMEOUT) as resp:
            return resp.status in (200, 206) and is_video(resp.read(64))
    except Exception:
        return False


def source_score(url):
    """Testa os links de uma fonte um por vez (contas IPTV limitam conexoes
    simultaneas e bloqueiam o IP se receberem muitas de uma vez)."""
    path = cache_path(url)
    links = sample_links(path, HEALTH_SAMPLES) if path.exists() else []
    ok = 0
    for link in links:
        ok += link_ok(link)
        time.sleep(1)
    log.info("  %s: %d/%d links com video", path.name, ok, len(links))
    return ok / len(links) if links else 0.0


def rank_sources():
    """Testa uma amostra de links de cada fonte e devolve as fontes vivas,
    das mais saudaveis para as menos (empate = ordem de SOURCES)."""
    with ThreadPoolExecutor(max_workers=len(SOURCES)) as pool:  # fontes em paralelo
        scores = dict(zip(SOURCES, pool.map(source_score, SOURCES)))
    alive = [u for u in SOURCES if scores[u] >= HEALTH_MIN]
    if not alive:
        log.warning("Nenhum servidor respondeu ao teste; usando todas as fontes")
        return list(SOURCES)
    dead = [cache_path(u).name for u in SOURCES if u not in alive]
    if dead:
        log.warning("Fontes fora do ar, ignoradas: %s", ", ".join(dead))
    return sorted(alive, key=lambda u: (-round(scores[u], 1), SOURCES.index(u)))


def build(order=SOURCES):
    """Le todas as fontes e agrupa as repeticoes.

    Devolve {kind: {group: [[extinf, [url_servidor1, url_servidor2, ...]], ...]}}.
    Cada titulo aparece uma vez; os links alternativos (de outros servidores)
    ficam guardados em ordem de prioridade para gerar as listas reserva.
    """
    seen_urls, by_key = set(), {}
    out = {}
    total = dup = adult = 0
    for url in order:
        path = cache_path(url)
        if not path.exists():
            continue
        for title, attrs, link in parse_m3u(path):
            total += 1
            group = norm_group(attrs.get("group-title", ""))
            kind = classify(link, group, title)
            if kind == "adultos" and not INCLUDE_ADULT:
                adult += 1
                continue
            key = (kind, norm_title(title))
            if link in seen_urls:
                dup += 1
                continue
            seen_urls.add(link)
            host = urlsplit(link).netloc
            if key in by_key:
                dup += 1
                entry = by_key[key]
                if host not in entry[2]:
                    entry[1].append(link)
                    entry[2].add(host)
                continue
            entry = [extinf_line(title, attrs, group, kind), [link], {host}]
            by_key[key] = entry
            out.setdefault(kind, {}).setdefault(group, []).append(entry)
    with_alt = sum(1 for e in by_key.values() if len(e[1]) > 1)
    log.info("Entradas lidas: %d | adultos removidos: %d | repetidas removidas: %d | unicas: %d"
             " | com servidor reserva: %d", total, adult, dup, total - adult - dup, with_alt)
    return out


def render(data, mirror):
    """Monta as linhas m3u usando o link de indice `mirror` (ou o ultimo disponivel)."""
    return {kind: {g: [f"{e[0]}\n{e[1][min(mirror, len(e[1]) - 1)]}\n" for e in entries]
                   for g, entries in groups.items()}
            for kind, groups in data.items()}


def slug(s):
    s = strip_accents(s).lower()
    s = re.sub(r"^(series|filmes|outros)\s*\|\s*", "", s)
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-") or "geral"


def write_chunks(base: Path, entries):
    """Escreve entries em base.m3u, dividindo em base_2.m3u... se passar do limite.

    Extensao .m3u (e nao .m3u8): o Kodi trata .m3u8 da internet como stream HLS e
    nao abre como lista; .m3u ele abre como pasta no navegador de arquivos."""
    files, buf, size, n = [], [], 0, 1

    def flush():
        name = base.with_name(base.name + ("" if n == 1 else f"_{n}") + ".m3u")
        name.parent.mkdir(parents=True, exist_ok=True)
        with open(name, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("#EXTM3U\n")
            fh.writelines(buf)
        files.append((name, len(buf)))

    for e in entries:
        b = len(e.encode("utf-8"))
        if buf and size + b > MAX_FILE_BYTES:
            flush()
            buf, size, n = [], 0, n + 1
        buf.append(e)
        size += b
    if buf:
        flush()
    return files


def write_set(out_dir: Path, data, split_kinds):
    """Escreve um conjunto completo de playlists em out_dir."""
    for f in [*out_dir.glob("*.m3u"), *out_dir.glob("*.m3u8")]:
        f.unlink()
    for d in OUT_DIRS:
        shutil.rmtree(out_dir / d, ignore_errors=True)

    def flat(kind):
        return [e for g in data.get(kind, {}).values() for e in g]

    def by_slug(kind):
        merged = {}
        for g, entries in data.get(kind, {}).items():
            merged.setdefault(slug(g), []).extend(entries)
        return merged

    written = []
    written += write_chunks(out_dir / "playlist", flat("canais"))
    written += write_chunks(out_dir / "adultos", flat("adultos"))
    # filmes e outros: arquivo unico se couber, senao um por grupo
    for kind in ("filmes", "outros"):
        if kind not in split_kinds:
            written += write_chunks(out_dir / kind, flat(kind))
        else:
            for s, entries in by_slug(kind).items():
                written += write_chunks(out_dir / kind / s, entries)
    for s, entries in by_slug("series").items():
        written += write_chunks(out_dir / "series" / s, entries)
    # copias .m3u8 dos enderecos ja cadastrados no Kodi (compatibilidade)
    for name in LEGACY_M3U8:
        if (out_dir / f"{name}.m3u").exists():
            shutil.copyfile(out_dir / f"{name}.m3u", out_dir / f"{name}.m3u8")
    return written


def write_outputs(data):
    main = render(data, 0)
    # decide a divisao pelo conjunto principal, para os nomes de arquivo baterem nos reservas
    split_kinds = {k for k in ("filmes", "outros")
                   if sum(len(e.encode()) for g in main.get(k, {}).values() for e in g)
                   > MAX_FILE_BYTES}
    for old in ROOT.glob("reserva*"):
        if old.is_dir() and old.name not in MIRRORS:
            shutil.rmtree(old, ignore_errors=True)

    written = []
    for i, name in enumerate(MIRRORS):
        written += write_set(ROOT / name if name else ROOT,
                             main if i == 0 else render(data, i), split_kinds)
    write_readme(sorted(written, key=lambda x: str(x[0])))
    write_indexes()
    return written


def write_indexes():
    """Gera index.html (formato de listagem de diretorio) em cada pasta, para o
    GitHub Pages servir um menu navegavel que o Kodi aceita como fonte de video."""
    (ROOT / ".nojekyll").touch()
    skip = {".git", ".cache", "logs", "__pycache__"}
    for d in [ROOT, *(p for p in ROOT.rglob("*") if p.is_dir())]:
        if skip & set(d.relative_to(ROOT).parts):
            continue
        subdirs = sorted(p.name for p in d.iterdir()
                         if p.is_dir() and p.name not in skip and any(p.rglob("*.m3u")))
        files = sorted(p.name for p in d.glob("*.m3u"))
        if not subdirs and not files:
            continue
        rel = "/" + ("" if d == ROOT else d.relative_to(ROOT).as_posix() + "/")
        links = ([f'<a href="{n}/">{n}/</a>' for n in subdirs]
                 + [f'<a href="{n}">{n}</a>' for n in files])
        html = (f'<html><head><meta charset="utf-8"><title>Index of {rel}</title></head>'
                f"<body><h1>Index of {rel}</h1><pre>\n" + "\n".join(links)
                + "\n</pre></body></html>\n")
        (d / "index.html").write_text(html, encoding="utf-8", newline="\n")


def write_readme(files):
    lines = [
        "# IPTV",
        "",
        "Playlists atualizadas automaticamente, sem repeticoes e divididas em arquivos menores.",
        "",
        "**Kodi (PVR IPTV Simple Client)** - use como URL da lista:",
        "",
        f"```\n{RAW_BASE}/playlist.m3u\n```",
        "",
        "**Menu** - Kodi > Videos > Arquivos > Adicionar videos > Procurar > Adicionar local",
        "de rede (servidor web HTTPS). Navegue pelas pastas e abra a lista desejada:",
        "",
        f"```\n{PAGES_BASE}/\n```",
        "",
        "**Servidor reserva** - mesmos titulos, links de outro servidor (quando existir).",
        "Cadastre como segunda instancia do IPTV Simple, desativada; ative se a principal cair:",
        "",
        "```\n" + "\n".join(f"{RAW_BASE}/{m}/playlist.m3u" for m in MIRRORS if m) + "\n```",
        "",
        f"Ultima atualizacao: {time.strftime('%Y-%m-%d %H:%M')}",
        "",
        "| Arquivo | Entradas | Tamanho |",
        "|---|---:|---:|",
    ]
    for path, n in files:
        rel = path.relative_to(ROOT).as_posix()
        lines.append(f"| [{rel}]({RAW_BASE}/{rel}) | {n} | {path.stat().st_size / 1e6:.1f} MB |")
    (ROOT / "README.md").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")


# ---------------------------------------------------------------- git

def git(*args, check=True):
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} falhou:\n{r.stdout}\n{r.stderr}")
    return r


def setup_git():
    if not (ROOT / ".git").exists():
        git("init", "-b", BRANCH)
        log.info("Repositorio git criado")
    remotes = git("remote").stdout.split()
    if "origin" in remotes:
        git("remote", "set-url", "origin", REPO_URL)
    else:
        git("remote", "add", "origin", REPO_URL)
    git("config", "user.name", GIT_NAME)
    git("config", "user.email", GIT_EMAIL)
    git("config", "core.autocrlf", "false")
    git("config", "http.postBuffer", "524288000")

    (ROOT / ".gitignore").write_text(".cache/\nlogs/\n__pycache__/\n*.part\n",
                                     encoding="utf-8", newline="\n")
    (ROOT / ".gitattributes").write_text("*.m3u text eol=lf\n*.m3u8 text eol=lf\n*.html text eol=lf\n", encoding="utf-8", newline="\n")

    # se o GitHub ja tem historico, sincroniza antes do primeiro commit local
    remote_head = git("ls-remote", "origin", BRANCH).stdout.strip()
    has_local = git("rev-parse", "--verify", "HEAD", check=False).returncode == 0
    if remote_head and not has_local:
        git("fetch", "origin", BRANCH)
        git("reset", "--mixed", f"origin/{BRANCH}")
        git("branch", "--set-upstream-to", f"origin/{BRANCH}", BRANCH, check=False)


def commit_and_push(message):
    git("add", "-A")
    if git("diff", "--cached", "--quiet", check=False).returncode == 0:
        log.info("Nada mudou nos arquivos gerados, sem commit")
        return
    git("commit", "-m", message)
    log.info("Commit criado: %s", message)
    r = git("push", "-u", "origin", BRANCH, check=False)
    if r.returncode != 0:
        log.warning("Push recusado, sincronizando com o GitHub e tentando de novo")
        git("pull", "--rebase", "-X", "theirs", "origin", BRANCH)
        git("push", "-u", "origin", BRANCH)
    log.info("Enviado para %s", REPO_URL)


# ---------------------------------------------------------------- agendador

def setup_schedule(hour):
    exe = Path(sys.executable)
    pyw = exe.with_name("pythonw.exe")
    if pyw.exists():
        exe = pyw
    script = Path(__file__).resolve()
    ps = f"""
$a = New-ScheduledTaskAction -Execute '{exe}' -Argument '"{script}" --run' -WorkingDirectory '{ROOT}'
$t = New-ScheduledTaskTrigger -Daily -At '{hour}'
$s = New-ScheduledTaskSettingsSet -StartWhenAvailable -AllowStartIfOnBatteries -DontStopIfGoingOnBatteries -RunOnlyIfNetworkAvailable -ExecutionTimeLimit (New-TimeSpan -Hours 2)
Register-ScheduledTask -TaskName '{TASK_NAME}' -Action $a -Trigger $t -Settings $s -Force | Out-Null
"""
    r = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                       capture_output=True, text=True)
    if r.returncode != 0:
        log.error("Falha ao criar tarefa agendada:\n%s", r.stderr)
    else:
        log.info("Tarefa '%s' agendada todo dia as %s (roda assim que possivel se o PC "
                 "estiver desligado no horario)", TASK_NAME, hour)


# ---------------------------------------------------------------- main

def update(force=False):
    log.info("Verificando fontes...")
    state = load_state()
    changed = [download(u, state) for u in SOURCES]
    log.info("Testando servidores...")
    order = rank_sources()
    order_changed = order != state.get("_order")
    state["_order"] = order
    save_state(state)
    generated = (ROOT / "playlist.m3u").exists()
    if not any(changed) and not order_changed and generated and not force:
        log.info("Nenhuma fonte mudou, nada a fazer")
        return
    log.info("Processando...")
    files = write_outputs(build(order))
    log.info("%d arquivos gerados (maior: %.1f MB)", len(files),
             max(p.stat().st_size for p, _ in files) / 1e6)
    commit_and_push(f"Atualiza playlists {time.strftime('%Y-%m-%d %H:%M')}")


def main():
    ap = argparse.ArgumentParser(description="Atualizador de playlists IPTV")
    ap.add_argument("--run", action="store_true", help="so atualiza (modo agendador)")
    ap.add_argument("--force", action="store_true", help="reprocessa mesmo sem mudancas")
    ap.add_argument("--hora", default=None, help=f"horario da tarefa diaria (padrao {DEFAULT_HOUR})")
    args = ap.parse_args()

    setup_logging()
    try:
        setup_git()
        if not args.run:
            setup_schedule(args.hora or DEFAULT_HOUR)
        elif args.hora:
            setup_schedule(args.hora)
        update(force=args.force)
        log.info("Concluido. Kodi: %s/playlist.m3u", RAW_BASE)
    except Exception:
        log.exception("Erro")
        sys.exit(1)


if __name__ == "__main__":
    main()
