#!/usr/bin/env python3
"""Build the anonymous CC 2027 supplementary archive and run its final gate.

All identities (repository paths, commits, the identity denylist) come from a
JSON configuration file kept outside this repository; see MAINTAINER.md.
"""
import argparse
import hashlib
import io
import json
import lzma
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile

PACKAGE_DIR = Path(__file__).resolve().parent.parent
TEMPLATE = PACKAGE_DIR / "template"
RECOVERED = PACKAGE_DIR / "recovered"
ARCHIVE_ROOT = "polcert"
ZIP_TIMESTAMP = (2026, 11, 18, 0, 0, 0)
TAR_MTIME = 1_794_960_000  # 2026-11-18T00:00:00Z
MAX_ARCHIVE_PATH_CHARS = 180
OMITTED = "(omitted for anonymous review)"

SOURCE_EXCLUDES = (
    ".github",
)
PLUTO_EXCLUDES = (
    "Dockerfile",
    "clan/vim_session.txt",
    "examples/pca/.pca.c.swp",
    "cloog-isl/test/reports",
    "polylib/doc/PI-1330.ps.gz",
    "polylib/doc/PI-785.ps.gz",
    "polylib/doc/doc.pdf.tar.gz",
    "polylib/doc/parampoly-doc.ps.gz",
)
TEXT_SUFFIXES = {
    "", ".c", ".cc", ".cpp", ".css", ".csv", ".h", ".html", ".in", ".json",
    ".log", ".loop", ".md", ".ml", ".mli", ".py", ".scop", ".sh", ".sizes",
    ".tsv", ".txt", ".v", ".yml", ".yaml", ".am", ".ac", ".cloog", ".js", ".env",
}
HEX_TOKEN = re.compile(rb"(?<![0-9A-Za-z])[0-9a-f]{7,40}(?![0-9A-Za-z])")
ANONYMIZED_URL = b"https://anonymized.invalid"


# ---------------------------------------------------------------------------
# helpers

def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    return sha256_bytes(Path(path).read_bytes())


def git(repo, *args, data=None):
    return subprocess.run(["git", "-C", str(repo), *args], input=data,
                          capture_output=True, check=True).stdout


def is_text(path, data):
    if b"\0" in data[:8192]:
        return False
    return path.suffix.lower() in TEXT_SUFFIXES or path.name in (
        "README", "LICENSE", "COPYING", "Makefile", "VERSION", ".gitmodules")


def tree_sha256(root):
    entries = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        entries.append("%s %s" % (path.relative_to(root).as_posix(), sha256_file(path)))
    return sha256_bytes("\n".join(entries).encode()), len(entries)


class Identity:
    """Denylist patterns plus commit resolution against local repositories."""

    def __init__(self, config):
        self.patterns = [re.compile(p.encode(), re.I) for p in config["denylist"]]
        self.literal_rewrites = [(re.compile(re.escape(k.encode()), re.I), v.encode())
                                 for k, v in config.get("rewrites", {}).items()]
        self.emails = {e.lower() for e in config["identity_emails"]}
        # URL prefixes to replace, e.g. "https://github.com/<owner>/".
        self.urls = [re.compile(re.escape(u.encode()) + rb"[^\s)>\]\"'`]*", re.I)
                     for u in config.get("url_prefixes", [])]
        self.repos = [Path(r).expanduser() for r in config["hash_repos"]]
        self.cache = {}

    def prefetch(self, tokens):
        pending = sorted({t.decode() for t in tokens} - set(self.cache))
        if not pending:
            return
        identifying = set()
        for repo in self.repos:
            query = "".join(t + "^{commit}\n" for t in pending).encode()
            proc = subprocess.run(["git", "-C", str(repo), "cat-file",
                                   "--batch-check=%(objectname)"],
                                  input=query, capture_output=True)
            resolved = {}
            for token, line in zip(pending, proc.stdout.decode().splitlines()):
                line = line.strip()
                if re.fullmatch(r"[0-9a-f]{40}", line):
                    resolved[token] = line
            if not resolved:
                continue
            shas = sorted(set(resolved.values()))
            log = subprocess.run(["git", "-C", str(repo), "log", "--no-walk=unsorted",
                                  "--stdin", "--format=%H %ae %ce"],
                                 input="\n".join(shas).encode() + b"\n",
                                 capture_output=True).stdout.decode()
            flagged = {parts[0] for parts in (l.split() for l in log.splitlines())
                       if len(parts) == 3 and {parts[1].lower(), parts[2].lower()} & self.emails}
            identifying |= {t for t, sha in resolved.items() if sha in flagged}
        for token in pending:
            self.cache[token] = token in identifying

    def commit_is_identifying(self, token):
        self.prefetch([token])
        return self.cache[token.decode()]

    def sanitize(self, data):
        for pattern in self.urls:
            data = pattern.sub(ANONYMIZED_URL, data)
        for pattern, replacement in self.literal_rewrites:
            data = pattern.sub(replacement, data)

        self.prefetch(HEX_TOKEN.findall(data))

        def hex_sub(match):
            return b"snapshot" if self.cache[match.group(0).decode()] else match.group(0)
        return HEX_TOKEN.sub(hex_sub, data)

    def findings(self, data):
        hits = [p.pattern.decode() for p in self.patterns if p.search(data)]
        tokens = HEX_TOKEN.findall(data)
        self.prefetch(tokens)
        hits += ["commit:" + t.decode() for t in set(tokens) if self.cache[t.decode()]]
        return hits


# ---------------------------------------------------------------------------
# assembly

def extract_git_tree(repo, commit, dest):
    dest.mkdir(parents=True, exist_ok=True)
    data = git(repo, "archive", "--format=tar", commit)
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        tar.extractall(dest)


def compose_recursive(repo, commit, dest):
    """git archive of repo@commit plus every submodule at its recorded commit."""
    extract_git_tree(repo, commit, dest)
    for line in git(repo, "ls-tree", "-r", commit).decode().splitlines():
        meta, path = line.split("\t", 1)
        mode, kind, sha = meta.split()
        if kind == "commit":
            compose_recursive(Path(repo) / path, sha, dest / path)


def remove_paths(root, relative_paths):
    removed = []
    for rel in relative_paths:
        target = root / rel
        if target.is_dir():
            shutil.rmtree(target)
            removed.append(rel)
        elif target.exists():
            target.unlink()
            removed.append(rel)
    return removed


def remove_elf(root):
    removed = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        with path.open("rb") as handle:
            if handle.read(4) == b"\x7fELF":
                removed.append(path.relative_to(root).as_posix())
                path.unlink()
    return removed


def sanitize_tree(root, identity, keep_suffixes=(".v",), report=None):
    changed = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        if path.suffix in keep_suffixes:
            continue
        data = path.read_bytes()
        if not is_text(path, data):
            continue
        if path.name == ".gitmodules":
            data_lines = data.splitlines(keepends=True)
            data_out = []
            for line in data_lines:
                if re.match(rb"\s*url\s*=", line) and any(p.search(line) for p in identity.urls):
                    line = re.sub(rb"=.*", b"= " + OMITTED.encode(), line)
                data_out.append(line)
            new = identity.sanitize(b"".join(data_out))
        else:
            new = identity.sanitize(data)
        if new != data:
            path.write_bytes(new)
            changed.append(path.relative_to(root).as_posix())
    if report is not None:
        report.extend(changed)
    return changed


def deterministic_tar_xz(src_root, out_path, prefix=""):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", format=tarfile.GNU_FORMAT) as tar:
        for path in sorted(src_root.rglob("*")):
            rel = path.relative_to(src_root).as_posix()
            name = (prefix + rel) if prefix else rel
            info = tar.gettarinfo(str(path), arcname=name)
            info.mtime = TAR_MTIME
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            if info.isdir():
                info.mode = 0o755
                tar.addfile(info)
            elif info.isreg():
                info.mode = 0o755 if os.access(path, os.X_OK) else 0o644
                with path.open("rb") as handle:
                    tar.addfile(info, handle)
            elif info.issym():
                raise RuntimeError("symlink in archive source: " + rel)
    out_path.write_bytes(lzma.compress(buffer.getvalue(), preset=6))


def copy_template(src, dest):
    if src.is_dir():
        shutil.copytree(src, dest, dirs_exist_ok=True)
    else:
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dest)


def split_report(text):
    """Drop the tracker line and the Fix section of an upstream bug report."""
    lines = [line for line in text.splitlines() if not line.startswith("**Tracker:**")]
    out, skipping = [], False
    for line in lines:
        if line.startswith("## "):
            skipping = line.strip().lower() == "## fix"
        if not skipping:
            out.append(line)
    body = "\n".join(out).rstrip() + "\n"
    blocks = re.findall(r"```c\n(.*?)```", body, re.S)
    return body, blocks


def fix_proof_links(stage):
    """Re-target links of the generated guides from their source-tree location."""
    proof = stage / "docs/proof"
    pattern = re.compile(r"""((?:href|src)=["'])([^"'#?]+)([^"']*["'])""")
    for path in sorted(proof.rglob("*.html")):
        rel = path.relative_to(proof)
        old_dir = PurePosixPath("source/doc/proof-html") / rel.parent.as_posix()
        new_dir = PurePosixPath("docs/proof") / rel.parent.as_posix()
        text = path.read_text(errors="replace")

        def fix(match):
            target = match.group(2)
            if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", target) or (path.parent / target).exists():
                return match.group(0)
            old_target = os.path.normpath(str(old_dir / target))
            if (stage / old_target).exists():
                return match.group(1) + os.path.relpath(old_target, str(new_dir)) + match.group(3)
            return match.group(0)
        new = pattern.sub(fix, text)
        if new != text:
            path.write_text(new)


def sanitize_recorded_archives(recorded, identity):
    """Sanitize text members of the recorded evidence archives and their index."""
    index_path = recorded / "archive-index.json"
    index = json.loads(index_path.read_text())
    changed_members = 0
    for name, entries in index.items():
        path = recorded / name
        mode = "r:xz" if name.endswith(".xz") else "r:gz"
        by_path = {entry["path"]: entry for entry in entries}
        members = []
        dirty = False
        with tarfile.open(path, mode) as tar:
            for member in tar:
                data = tar.extractfile(member).read() if member.isfile() else None
                if data is not None and is_text(Path(member.name), data):
                    new = identity.sanitize(data)
                    if new != data:
                        dirty = True
                        changed_members += 1
                        data = new
                        entry = by_path.get(member.name)
                        if entry is not None:
                            entry["sha256"] = sha256_bytes(data)
                            entry["bytes"] = len(data)
                            entry["anonymized"] = True
                        member.size = len(data)
                members.append((member, data))
        if not dirty:
            continue
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w", format=tarfile.GNU_FORMAT) as tar:
            for member, data in members:
                tar.addfile(member, io.BytesIO(data) if data is not None else None)
        raw = buffer.getvalue()
        if name.endswith(".xz"):
            path.write_bytes(lzma.compress(raw, preset=6))
        else:
            import gzip
            path.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
    index_path.write_text(json.dumps(index, indent=1, sort_keys=True) + "\n")
    return changed_members


def build_bugs(stage, cfg):
    catalog = json.loads((TEMPLATE / "bugs/catalog.json").read_text())
    reports = Path(cfg["bug_reports"]).expanduser()
    bugs = stage / "bugs"
    rows_rejected, rows_codegen = [], []
    for group, rows in (("rejected", rows_rejected), ("codegen", rows_codegen)):
        for index, entry in enumerate(catalog[group], start=1):
            body, blocks = split_report((reports / entry["report"]).read_text())
            directory = bugs / group / entry["dir"]
            directory.mkdir(parents=True)
            for number, block in enumerate(blocks, start=1):
                name = "repro.c" if number == 1 else "repro-%d.c" % number
                (directory / name).write_text(block)
            body += "\n## PolCert\n\n" + entry["polcert"] + "\n"
            (directory / "README.md").write_text(body)
            title = body.splitlines()[0].lstrip("# ").strip()
            rows.append((index, entry, title))
    lines = [
        "# Miscompilation Study", "",
        "Each directory holds one Pluto miscompilation: Pluto exits normally and the",
        "generated code computes a different result than the source. Every case was",
        "confirmed by execution on the development head of upstream Pluto",
        "(commit 2b6fd99 of 2026-11-05) and, unless the report says otherwise, on",
        "release 0.13.1. The historical snapshot in `third_party/pluto/historical.tar.xz`",
        "contains the defects; the fixed snapshot repairs or refuses them.", "",
        "## Rejected by PolCert (Table 3)", "",
        "| Defect | Validator | Outcome | Directory |", "| --- | --- | --- | --- |",
    ]
    for _, entry, _ in rows_rejected:
        lines.append("| %s | %s | %s | [`rejected/%s`](rejected/%s/README.md) |" % (
            entry["table_row"], entry["validator"].replace("_", "\\_"), entry["outcome"],
            entry["dir"], entry["dir"]))
    lines += [
        "", "`docker run --rm polcert-artifact bugs` replays all seven with the historical",
        "and the fixed Pluto snapshots and exits with status 0 when every outcome",
        "matches the table.", "",
        "## In Pluto's code generation and annotation", "",
        "PolCert generates loops with its verified generator and marks only certified",
        "coordinates as parallel; it does not use Pluto's generated C, loop annotations or",
        "unroll-and-jam. These reports reproduce with upstream Pluto alone.", "",
        "| Defect | Directory |", "| --- | --- |",
    ]
    for _, entry, _ in rows_codegen:
        lines.append("| %s | [`codegen/%s`](codegen/%s/README.md) |" % (
            entry["summary"], entry["dir"], entry["dir"]))
    (bugs / "README.md").write_text("\n".join(lines) + "\n")


def build_evaluation(stage, cfg, identity):
    freeze = Path(cfg["freeze_dir"]).expanduser()
    reviewed = Path(cfg["reviewed_supplement_dir"]).expanduser()
    evaluation = stage / "evaluation"
    copy_template(TEMPLATE / "evaluation", evaluation)
    recorded = evaluation / "recorded"
    recorded.mkdir(parents=True)
    for path in sorted((reviewed / "evaluation/results").iterdir()):
        if path.name != "index.html":
            shutil.copy2(path, recorded / path.name)
    for path in sorted((reviewed / "evaluation/evidence").iterdir()):
        shutil.copy2(path, recorded / path.name)
    sanitize_recorded_archives(recorded, identity)
    rerun = evaluation / "rerun"
    shutil.copytree(freeze / "table1", rerun, dirs_exist_ok=True)
    for path in sorted((freeze / "iss").iterdir()):
        shutil.copy2(path, rerun / path.name)
    shutil.copytree(freeze / "phase2", rerun / "build-and-tests")
    scripts = rerun / "scripts"
    scripts.mkdir()
    for name in cfg["freeze_scripts"]:
        shutil.copy2(freeze / "scripts" / name, scripts / name)
    shutil.copytree(freeze / "timing", evaluation / "timing-rerun")
    sanitize_tree(rerun, identity, keep_suffixes=())
    sanitize_tree(evaluation / "timing-rerun", identity, keep_suffixes=())


def build(cfg, stage):
    identity = Identity(cfg)
    stage.mkdir(parents=True)
    manifest = {"snapshot": cfg["snapshot_label"]}

    # source
    source = stage / "source"
    extract_git_tree(Path(cfg["polcert_repo"]).expanduser(), cfg["polcert_commit"], source)
    removed = remove_paths(source, SOURCE_EXCLUDES) + ["ELF:" + p for p in remove_elf(source)]
    sanitized = sanitize_tree(source, identity)
    formal = {p.relative_to(source).as_posix(): sha256_file(p)
              for p in sorted(source.rglob("*.v"))}
    manifest["formal_source"] = {
        "files": len(formal),
        "tree_sha256": sha256_bytes("\n".join("%s %s" % kv for kv in formal.items()).encode()),
        "packaging_check": "byte-identical-to-frozen-commit",
        "removed": removed,
        "sanitized_non_formal_files": sanitized,
    }
    (stage / "FORMAL_SOURCES.sha256.json").write_text(json.dumps(formal, indent=1, sort_keys=True) + "\n")

    # Pluto snapshots
    pluto_dir = stage / "third_party/pluto"
    pluto_dir.mkdir(parents=True)
    manifest["pluto_sources"] = {}
    for label in ("fixed", "historical"):
        with tempfile.TemporaryDirectory(prefix="pluto-" + label + "-") as tmp:
            tree = Path(tmp) / "tree"
            compose_recursive(Path(cfg["pluto_repo"]).expanduser(), cfg["pluto_" + label], tree)
            excluded = remove_paths(tree, PLUTO_EXCLUDES)
            elf = remove_elf(tree)
            changed = sanitize_tree(tree, identity, keep_suffixes=())
            digest, files = tree_sha256(tree)
            archive = pluto_dir / (label + ".tar.xz")
            deterministic_tar_xz(tree, archive)
            manifest["pluto_sources"][label] = {
                "archive": "third_party/pluto/%s.tar.xz" % label,
                "files": files, "tree_sha256": digest,
                "packaging_archive_sha256": sha256_file(archive),
                "excluded": excluded, "removed_elf": elf, "sanitized_files": changed,
            }

    # environment and top-level files
    copy_template(TEMPLATE / "environment", stage / "environment")
    shutil.copy2(RECOVERED / "environment/run-paper-bugs.py", stage / "environment/run-paper-bugs.py")
    shutil.copy2(TEMPLATE / "README.md", stage / "README.md")
    shutil.copy2(TEMPLATE / "dockerignore", stage / ".dockerignore")
    shutil.copy2(source / "LICENSE", stage / "LICENSE")
    shutil.copytree(source / "licenses", stage / "licenses")
    third = (source / "THIRD_PARTY.md").read_text()
    third += ("\n## Pluto snapshots\n\n`third_party/pluto/fixed.tar.xz` and "
              "`third_party/pluto/historical.tar.xz` contain Pluto and its bundled "
              "dependencies (CLooG, isl, PET, Clan, Candl, OpenScop, PipLib, PolyLib) "
              "with their license files. Pluto is distributed under the MIT license "
              "([licenses/Pluto-MIT.txt](licenses/Pluto-MIT.txt)).\n")
    (stage / "THIRD_PARTY.md").write_text(third.replace("](LICENSE)", "](LICENSE)")
                                          .replace("](VPL/LICENSE)", "](source/VPL/LICENSE)")
                                          .replace("](licenses/LGPL-3.0.txt)", "](licenses/LGPL-3.0.txt)"))

    # documentation
    proof = Path(cfg["proof_html"]).expanduser()
    if proof.is_dir():
        shutil.copytree(proof, stage / "docs/proof")
        sanitize_tree(stage / "docs/proof", identity, keep_suffixes=())
        fix_proof_links(stage)
        manifest["proof_html"] = {"files": sum(1 for p in (stage / "docs/proof").rglob("*") if p.is_file())}
    else:
        manifest["proof_html"] = None

    build_evaluation(stage, cfg, identity)
    build_bugs(stage, cfg)
    sanitize_tree(stage / "bugs", identity, keep_suffixes=())

    files = []
    for path in sorted(p for p in stage.rglob("*") if p.is_file()):
        rel = path.relative_to(stage).as_posix()
        files.append({"path": rel, "bytes": path.stat().st_size, "sha256": sha256_file(path)})
    manifest["files"] = len(files)
    (stage / "MANIFEST.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    (stage / "PACKAGED_FILES.json").write_text(json.dumps(files, indent=1) + "\n")


def write_zip(stage, out):
    out.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(out, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(stage.rglob("*")):
            rel = path.relative_to(stage).as_posix()
            name = ARCHIVE_ROOT + "/" + rel + ("/" if path.is_dir() else "")
            info = zipfile.ZipInfo(name, ZIP_TIMESTAMP)
            if path.is_dir():
                info.external_attr = (0o40755 << 16) | 0x10
                archive.writestr(info, b"")
            else:
                mode = 0o755 if os.access(path, os.X_OK) else 0o644
                info.external_attr = (0o100000 | mode) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(info, path.read_bytes())


# ---------------------------------------------------------------------------
# gate

def archive_members(path, data):
    """Yield (name, bytes) for members of supported archives."""
    suffixes = "".join(PurePosixPath(path).suffixes[-2:])
    try:
        if suffixes.endswith(".tar.xz") or suffixes.endswith(".tar.gz") or suffixes.endswith(".tgz"):
            mode = "r:xz" if suffixes.endswith(".xz") else "r:gz"
            with tarfile.open(fileobj=io.BytesIO(data), mode=mode) as tar:
                for member in tar:
                    if member.issym() or member.islnk():
                        yield member.name, b"<link>" + member.linkname.encode()
                    elif member.isfile():
                        yield member.name, tar.extractfile(member).read()
        elif path.endswith(".zip"):
            with zipfile.ZipFile(io.BytesIO(data)) as inner:
                for name in inner.namelist():
                    yield name, inner.read(name)
    except (tarfile.TarError, zipfile.BadZipFile, EOFError, lzma.LZMAError) as error:
        yield path + ":<unreadable>", str(error).encode()


LINK_PATTERNS = (
    re.compile(r"\]\(([^)\s]+)\)"),
    re.compile(r"""(?:href|src)=["']([^"']+)["']"""),
)


def check_links(root):
    broken = []
    for path in sorted(p for p in root.rglob("*") if p.suffix in (".md", ".html")
                       and not p.relative_to(root).as_posix().startswith("source/")):
        text = path.read_text(errors="replace")
        for pattern in LINK_PATTERNS:
            for target in pattern.findall(text):
                if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", target) or target.startswith("#"):
                    continue
                target = target.split("#", 1)[0].split("?", 1)[0]
                if not target:
                    continue
                if not (path.parent / target).exists():
                    broken.append("%s -> %s" % (path.relative_to(root).as_posix(), target))
    return broken


def gate(zip_path, cfg):
    identity = Identity(cfg)
    results = {}
    with zipfile.ZipFile(zip_path) as archive:
        results["zip_testzip"] = archive.testzip() is None
        names = archive.namelist()
        results["long_paths"] = [n for n in names if len(n) > MAX_ARCHIVE_PATH_CHARS]
        results["symlinks"] = [i.filename for i in archive.infolist()
                               if (i.external_attr >> 16) & 0o170000 == 0o120000]
        with tempfile.TemporaryDirectory(prefix="cc27-gate-") as tmp:
            archive.extractall(tmp)
            root = Path(tmp) / ARCHIVE_ROOT
            # formal sources
            repo, commit = Path(cfg["polcert_repo"]).expanduser(), cfg["polcert_commit"]
            expected = [p for p in git(repo, "ls-tree", "-r", "--name-only", commit).decode().splitlines()
                        if p.endswith(".v")]
            mismatched = []
            for rel in expected:
                path = root / "source" / rel
                blob = git(repo, "show", "%s:%s" % (commit, rel))
                if not path.is_file() or path.read_bytes() != blob:
                    mismatched.append(rel)
            shipped = sorted(p.relative_to(root / "source").as_posix()
                             for p in (root / "source").rglob("*.v"))
            results["formal_sources"] = {"expected": len(expected), "shipped": len(shipped),
                                         "mismatched": mismatched,
                                         "extra": sorted(set(shipped) - set(expected))}
            # JSON
            bad_json = []
            for path in root.rglob("*.json"):
                try:
                    json.loads(path.read_text())
                except (ValueError, UnicodeDecodeError) as error:
                    bad_json.append("%s: %s" % (path.relative_to(root), error))
            results["invalid_json"] = bad_json
            results["broken_links"] = check_links(root)
            # ELF and identity, including archive members
            elf, identity_hits = [], []
            for path in sorted(p for p in root.rglob("*") if p.is_file()):
                rel = path.relative_to(root).as_posix()
                data = path.read_bytes()
                if data[:4] == b"\x7fELF":
                    elf.append(rel)
                hits = identity.findings(data)
                if hits:
                    identity_hits.append({"file": rel, "hits": sorted(set(hits))})
                for member, member_data in archive_members(rel, data):
                    if member_data[:4] == b"\x7fELF":
                        elf.append(rel + "!" + member)
                    hits = identity.findings(member_data) + identity.findings(member.encode())
                    if hits:
                        identity_hits.append({"file": rel + "!" + member, "hits": sorted(set(hits))})
            results["elf"] = elf
            results["identity"] = identity_hits
            pdfs = [p.relative_to(root).as_posix() for p in root.rglob("*.pdf")]
            results["pdfs"] = pdfs
    results["passed"] = (results["zip_testzip"] and not results["long_paths"]
                         and not results["symlinks"]
                         and not results["formal_sources"]["mismatched"]
                         and not results["formal_sources"]["extra"]
                         and results["formal_sources"]["expected"] == results["formal_sources"]["shipped"]
                         and not results["invalid_json"] and not results["broken_links"]
                         and not results["elf"] and not results["identity"] and not results["pdfs"])
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--gate-only", action="store_true")
    parser.add_argument("--keep-stage", type=Path)
    args = parser.parse_args()
    cfg = json.loads(args.config.read_text())
    if not args.gate_only:
        with tempfile.TemporaryDirectory(prefix="cc27-stage-") as tmp:
            stage = Path(tmp) / ARCHIVE_ROOT
            build(cfg, stage)
            write_zip(stage, args.output)
            if args.keep_stage:
                if args.keep_stage.exists():
                    shutil.rmtree(args.keep_stage)
                shutil.copytree(stage, args.keep_stage)
    results = gate(args.output, cfg)
    report = args.output.with_suffix(".gate.json")
    report.write_text(json.dumps(results, indent=2) + "\n")
    summary = {k: (len(v) if isinstance(v, list) else v) for k, v in results.items()}
    print(json.dumps(summary, indent=1))
    print("zip:", args.output, args.output.stat().st_size, "bytes", sha256_file(args.output))
    return 0 if results["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
