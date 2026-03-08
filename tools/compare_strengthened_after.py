#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import tempfile

ROOT = pathlib.Path('/polcert')
PLUTO_FLAGS = [
    '--dumpscop',
    '--nointratileopt',
    '--nodiamond-tile',
    '--noprevector',
    '--smartfuse',
    '--nounrolljam',
    '--noparallel',
    '--notile',
    '--rar',
    '--readscop',
]
BEGIN = '== Debug Extracted OpenScop ==\n'
END = '== Debug Roundtrip-Before OpenScop ==\n'


def run(cmd: list[str], cwd: pathlib.Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=True)


def parse_scop(path: pathlib.Path) -> dict[str, list[str]]:
    domain_meta = []
    scattering_meta = []
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line in {'DOMAIN', 'SCATTERING'}:
            j = i + 1
            while j < len(lines):
                nxt = lines[j].strip()
                if nxt == '' or nxt.startswith('#'):
                    j += 1
                    continue
                if line == 'DOMAIN':
                    domain_meta.append(nxt)
                else:
                    scattering_meta.append(nxt)
                break
            i = j
        i += 1
    return {'domain_meta': domain_meta, 'scattering_meta': scattering_meta}


def extract_strengthened_before(case: str, work: pathlib.Path) -> pathlib.Path:
    loop_path = ROOT / 'tests' / 'polopt-generated' / 'inputs' / f'{case}.loop'
    proc = run([str(ROOT / 'polopt'), '--debug-scheduler', str(loop_path)], cwd=ROOT)
    txt = proc.stdout
    start = txt.index(BEGIN) + len(BEGIN)
    end = txt.index(END, start)
    body = txt[start:end].strip() + '\n'
    out = work / 'strengthened.before.scop'
    out.write_text(body)
    return out


def run_pluto_readscop(inp: pathlib.Path, work: pathlib.Path) -> pathlib.Path:
    target = work / 'in.scop'
    shutil.copy2(inp, target)
    subprocess.run(['pluto', *PLUTO_FLAGS, str(target)], cwd=work, text=True, capture_output=True, check=True)
    candidates = [
        work / 'in.afterscheduling.scop',
        work / 'in.scop.afterscheduling.scop',
    ]
    for c in candidates:
        if c.exists():
            return c
    raise FileNotFoundError(f'no afterscheduling scop for {inp}')


def extract_c_after(case: str, work: pathlib.Path) -> pathlib.Path:
    src = ROOT / 'tests' / 'pluto-all' / case / f'{case}.c'
    in_c = work / 'in.c'
    shutil.copy2(src, in_c)
    subprocess.run([
        'pluto', '--dumpscop', '--nointratileopt', '--nodiamond-tile', '--noprevector',
        '--smartfuse', '--nounrolljam', '--noparallel', '--notile', '--rar', str(in_c)
    ], cwd=work, text=True, capture_output=True, check=True)
    for c in [work / 'in.afterscheduling.scop', work / 'in.c.afterscheduling.scop']:
        if c.exists():
            return c
    raise FileNotFoundError(f'no C-path after for {case}')


def case_names() -> list[str]:
    inputs = ROOT / 'tests' / 'polopt-generated' / 'inputs'
    return sorted(p.stem for p in inputs.glob('*.loop'))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--output-json', required=True)
    ap.add_argument('--output-md', required=True)
    args = ap.parse_args()

    rows = []
    raw = {'cases': []}
    dom_mismatch = 0
    scat_mismatch = 0

    with tempfile.TemporaryDirectory(prefix='polcert-strengthened-after-') as td:
        base = pathlib.Path(td)
        for case in case_names():
            work = base / case
            work.mkdir(parents=True, exist_ok=True)
            our_before = extract_strengthened_before(case, work)
            our_after = run_pluto_readscop(our_before, work)
            c_after = extract_c_after(case, work)
            our = parse_scop(our_after)
            c = parse_scop(c_after)
            dom_ok = our['domain_meta'] == c['domain_meta']
            scat_ok = our['scattering_meta'] == c['scattering_meta']
            if not dom_ok:
                dom_mismatch += 1
            if not scat_ok:
                scat_mismatch += 1
            raw['cases'].append({
                'case': case,
                'our_after': our,
                'c_after': c,
                'after_domain_match': dom_ok,
                'after_scattering_match': scat_ok,
            })
            rows.append(
                '| {case} | {dom} | {scat} | `{od}` | `{cd}` | `{os}` | `{cs}` |'.format(
                    case=case,
                    dom='yes' if dom_ok else 'no',
                    scat='yes' if scat_ok else 'no',
                    od='; '.join(our['domain_meta']),
                    cd='; '.join(c['domain_meta']),
                    os='; '.join(our['scattering_meta']),
                    cs='; '.join(c['scattering_meta']),
                )
            )

    pathlib.Path(args.output_json).write_text(json.dumps(raw, indent=2, sort_keys=True) + '\n')
    pathlib.Path(args.output_md).write_text('\n'.join([
        '# Strengthened Raw After Comparison',
        '',
        'Date: 2026-03-08',
        '',
        'Comparison method:',
        '- our path: `polopt --debug-scheduler` slice strengthened source `before.scop`, then `pluto --readscop`',
        '- c path: `tests/pluto-all/<case>/<case>.c` -> `pluto` with README flags',
        '- compare raw Pluto `after.scop` only',
        '',
        f'- cases compared: `{len(rows)}`',
        f'- after domain mismatches: `{dom_mismatch}`',
        f'- after scattering mismatches: `{scat_mismatch}`',
        '',
        '| case | after domain | after scattering | our after domain | c after domain | our after scattering | c after scattering |',
        '| --- | --- | --- | --- | --- | --- | --- |',
        *rows,
        '',
    ]) + '\n')


if __name__ == '__main__':
    main()
