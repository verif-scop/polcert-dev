#!/usr/bin/env python3
"""Replay unchanged assertions while archiving their normally temporary files."""
import argparse
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import traceback


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--buggy-root', type=Path, required=True)
    parser.add_argument('--fixed-pluto', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root, out = args.source_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    buggy = args.buggy_root.resolve()
    os.environ.update(POLCERT_BUGGY_PLUTO=str(buggy / 'tool/pluto'),
                      POLCERT_BUGGY_POLYCC=str(buggy / 'polycc'),
                      POLCERT_PLUTO=str(args.fixed_pluto.resolve()),
                      COMPCERT_CONFIG=str(root / 'tests/pluto/polcert.ini'))
    binaries = {name: sha(root / name) for name in ('polopt', 'polcert')}
    scripts = ['run_auto_affine_lp_cc_scaling', 'run_vanished_outer_parallel',
               'run_notile_unrolljam_nonpermutable', 'run_tiling_innerpar_satvec',
               'run_tiling_mixed_depth_cross_band']
    sys.path.insert(0, str(root / 'tools/pluto_bugs'))
    results = []
    for index, name in enumerate(scripts):
        directory = out / name
        directory.mkdir()
        script = root / 'tools/pluto_bugs' / (name + '.py')
        spec = importlib.util.spec_from_file_location('replay_' + str(index), script)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        real_run, real_temporary = module.run, tempfile.TemporaryDirectory
        calls = []
        @contextlib.contextmanager
        def retained_workdir(*positional, **keywords):
            path = tempfile.mkdtemp(prefix=keywords.get('prefix', 'work-'), dir=directory)
            yield path
        def recorded_run(command, **kwargs):
            call = directory / ('command-%03d' % len(calls))
            call.mkdir()
            record = {'command': [str(x) for x in command],
                      'cwd': str(kwargs.get('cwd') or os.getcwd()),
                      'timeout': kwargs.get('timeout', 'runner-default')}
            try:
                result = real_run(command, **kwargs)
                (call / 'combined-output.txt').write_text(result.stdout or '')
                record['returncode'] = result.returncode
                return result
            finally:
                calls.append(record)
                (call / 'command.json').write_text(json.dumps(record, indent=2) + '\n')
        module.run = recorded_run
        tempfile.TemporaryDirectory = retained_workdir
        result = {'case': name, 'script_sha256': sha(script)}
        try:
            with (directory / 'runner.stdout.txt').open('w') as stdout, (directory / 'runner.stderr.txt').open('w') as stderr:
                with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                    try:
                        result['returncode'] = module.main()
                    except Exception as error:
                        result.update(returncode=1, error=str(error))
                        traceback.print_exc()
        finally:
            tempfile.TemporaryDirectory = real_temporary
        result['calls'] = calls
        results.append(result)
        if binaries != {name: sha(root / name) for name in binaries}:
            raise RuntimeError('replay changed a frozen compiler binary')
        (out / 'summary.json').write_text(json.dumps({
            'binary_sha256': binaries,
            'historical_pluto_sha256': sha(buggy / 'tool/pluto'),
            'historical_polycc_sha256': sha(buggy / 'polycc'),
            'fixed_pluto_sha256': sha(args.fixed_pluto),
            'producer_contract': 'The unchanged runners explicitly use the historical producer for bug candidates; fixed Pluto is only the inherited default.',
            'assertions_changed': False, 'temporary_workdirs_preserved': True,
            'rows': results,
        }, indent=2) + '\n')
        print(json.dumps({key: result[key] for key in ('case', 'returncode', 'error') if key in result}), flush=True)
    return 0 if all(result['returncode'] == 0 for result in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
