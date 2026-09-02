#!/usr/bin/env python3
"""Freeze exact program pairs produced by the v10 test configurations.

The normal test runners check complete optimizer output and then retain only a
one-line verdict.  This companion collector reruns the same fixed fixtures and
arguments, preserving the input and the accepted output for the reviewer-facing
artifact.  It is intentionally separate from the trusted compiler and proof
source.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any


OPTIMIZED_MARKER = "== Optimized Loop =="
FROZEN_POLOPT_SHA256 = "2ba773fc600b69df22d934945088092ba851d4ba6f5035b6d22ab9347a2c4438"
FROZEN_PLUTO_SHA256 = "87053c7373078991f9e70eba686b06a192df61033885134dba2d2beada88aff2"
FROZEN_BUGGY_POLYCC_SHA256 = "1bf3bdedccbbf918b87f2b0cf7a9c727dfa522d36b67868d98434b2840ce423d"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def optimized_loop(stdout: str) -> str | None:
    start = stdout.find(OPTIMIZED_MARKER)
    if start < 0:
        return None
    text = stdout[start + len(OPTIMIZED_MARKER) :].lstrip("\r\n")
    return text.rstrip() + "\n"


def fixture_text(paths: list[Path]) -> str:
    if len(paths) == 1:
        return paths[0].read_text(encoding="utf-8")
    chunks = []
    for path in paths:
        chunks.append(f"/* {path.name} */\n{path.read_text(encoding='utf-8').rstrip()}")
    return "\n\n".join(chunks) + "\n"


class Collector:
    def __init__(
        self,
        source: Path,
        output: Path,
        timeout: int,
        expected_polopt_sha256: str,
        replace_existing: bool,
    ) -> None:
        self.source = source.resolve()
        self.output = output.resolve()
        self.timeout = timeout
        self.replace_existing = replace_existing
        self.output.mkdir(parents=True, exist_ok=True)
        self.programs = self.output / "programs"
        self.programs.mkdir(exist_ok=True)
        self.records: dict[tuple[str, str], dict[str, object]] = {}
        self.failures: list[str] = []
        self.env = os.environ.copy()
        self.env.setdefault(
            "COMPCERT_CONFIG", str(self.source / "tests/pluto/polcert.ini")
        )
        self.polopt_sha256 = hashlib.sha256(
            (self.source / "polopt").read_bytes()
        ).hexdigest()
        require(
            self.polopt_sha256 == expected_polopt_sha256,
            "polopt binary does not match the frozen Release image: "
            f"expected {expected_polopt_sha256}, got {self.polopt_sha256}",
        )
        self.pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
        self.buggy_polycc = Path(
            os.environ.get("POLCERT_BUGGY_POLYCC", "/opt/polcert/pluto-buggy/polycc")
        )
        require(self.pluto.is_file(), f"missing fixed Pluto: {self.pluto}")
        require(self.buggy_polycc.is_file(), f"missing historical polycc: {self.buggy_polycc}")
        self.pluto_sha256 = hashlib.sha256(self.pluto.read_bytes()).hexdigest()
        self.buggy_polycc_sha256 = hashlib.sha256(
            self.buggy_polycc.read_bytes()
        ).hexdigest()
        require(
            self.pluto_sha256 == FROZEN_PLUTO_SHA256,
            f"fixed Pluto hash mismatch: {self.pluto_sha256}",
        )
        require(
            self.buggy_polycc_sha256 == FROZEN_BUGGY_POLYCC_SHA256,
            f"historical polycc hash mismatch: {self.buggy_polycc_sha256}",
        )

    def load_existing(self) -> None:
        index = self.output / "index.json"
        require(index.is_file(), f"cannot append without {index}")
        for record in json.loads(index.read_text(encoding="utf-8"))["pairs"]:
            key = (str(record["suite"]), str(record["case"]))
            require(key not in self.records, f"duplicate existing pair: {key}")
            self.records[key] = record

    def add_pair(
        self,
        suite: str,
        case: str,
        before: str,
        after: str,
        *,
        left_label: str = "Before Program",
        right_label: str = "Accepted Program",
        extension: str = "loop",
        command: list[str] | None = None,
        note: str | None = None,
        kind: str = "accepted-program-pair",
    ) -> None:
        key = (suite, case)
        require(
            key not in self.records or self.replace_existing,
            f"duplicate program pair: {suite}/{case}",
        )
        digest = hashlib.sha256(f"{suite}\0{case}".encode()).hexdigest()[:14]
        case_dir = self.programs / digest
        case_dir.mkdir(exist_ok=True)
        before_path = case_dir / f"before.{extension}"
        after_path = case_dir / f"after.{extension}"
        before_path.write_text(before.rstrip() + "\n", encoding="utf-8")
        after_path.write_text(after.rstrip() + "\n", encoding="utf-8")
        record: dict[str, object] = {
            "suite": suite,
            "case": case,
            "before": before_path.relative_to(self.output).as_posix(),
            "after": after_path.relative_to(self.output).as_posix(),
            "left_label": left_label,
            "right_label": right_label,
            "kind": kind,
        }
        if command:
            record["command"] = command
        if note:
            record["note"] = note
        self.records[key] = record

    def run_polopt(
        self,
        suite: str,
        case: str,
        inputs: list[Path],
        args: list[str],
        *,
        timeout: int | None = None,
        env: dict[str, str] | None = None,
        cwd: Path | None = None,
        command_prefix: list[str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        executable = self.source / "polopt"
        command = [
            str(executable),
            *(command_prefix or []),
            *args,
            *(str(path) for path in inputs),
        ]
        run_env = self.env.copy()
        if env:
            run_env.update(env)
        if cwd is not None:
            return subprocess.run(
                command,
                cwd=cwd,
                env=run_env,
                text=True,
                capture_output=True,
                timeout=timeout or self.timeout,
                check=False,
            )
        with tempfile.TemporaryDirectory(prefix="polcert-program-view-") as temporary:
            return subprocess.run(
                command,
                cwd=temporary,
                env=run_env,
                text=True,
                capture_output=True,
                timeout=timeout or self.timeout,
                check=False,
            )

    def collect_loop_command(
        self,
        suite: str,
        case: str,
        inputs: list[Path],
        args: list[str],
        *,
        timeout: int | None = None,
        env: dict[str, str] | None = None,
        cwd: Path | None = None,
        command_prefix: list[str] | None = None,
    ) -> None:
        try:
            proc = self.run_polopt(
                suite,
                case,
                inputs,
                args,
                timeout=timeout,
                env=env,
                cwd=cwd,
                command_prefix=command_prefix,
            )
        except subprocess.TimeoutExpired:
            self.failures.append(f"{suite}/{case}: timed out")
            return
        after = optimized_loop(proc.stdout)
        if proc.returncode != 0 or after is None:
            self.failures.append(
                f"{suite}/{case}: exit={proc.returncode}, optimized={after is not None}\n"
                f"stderr:\n{proc.stderr[-2000:]}"
            )
            return
        public_command = [
            "./polopt",
            *(command_prefix or []),
            *args,
            *(path.name for path in inputs),
        ]
        self.add_pair(
            suite,
            case,
            fixture_text(inputs),
            after,
            command=public_command,
        )

    def collect_manifest(self, suite: str, manifest_path: Path) -> None:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        fixtures = {
            name: (manifest_path.parent / path).resolve()
            for name, path in data["fixtures"].items()
        }
        accepted = 0
        for spec in data["checks"]:
            if spec["expect"] != "success":
                continue
            fixture_names = spec.get("input_fixtures", [spec.get("fixture")])
            inputs = [fixtures[name] for name in fixture_names]
            self.collect_loop_command(
                suite,
                spec["name"],
                inputs,
                list(spec.get("args", [])),
                timeout=data.get("timeout_seconds", self.timeout),
            )
            accepted += 1
        print(f"[{suite}] collected {accepted}", flush=True)

    def collect_manifests(self) -> None:
        manifests = (
            (
                "parallel-loop validation",
                self.source / "tools/parallel_current/suite_manifest.json",
            ),
            (
                "innermost parallel-loop validation",
                self.source / "tools/vector_current/suite_manifest.json",
            ),
            (
                "two-level tiling configurations",
                self.source / "tools/second_level_tiling/suite_manifest.json",
            ),
        )
        for suite, manifest in manifests:
            self.collect_manifest(suite, manifest)

    def collect_one_level(self) -> None:
        module = load_module(
            "program_views_one_level",
            self.source / "tools/tiling_routes/check_non_second_level_routes.py",
        )
        accepted = [case for case in module.route_cases() if case.expect_success]
        require(len(accepted) == 84, f"expected 84 one-level outputs, got {len(accepted)}")
        for case in accepted:
            self.collect_loop_command(
                "one-level tiling configurations",
                case.name,
                [case.fixture],
                list(case.args),
            )
        print("[one-level tiling configurations] collected 84", flush=True)

    def collect_identity_iss(self) -> None:
        fixtures = sorted((self.source / "tests/polopt-regression/inputs").glob("*.loop"))
        require(len(fixtures) == 71, f"expected 71 identity ISS fixtures, got {len(fixtures)}")
        base_args = [
            "--pluto-compat",
            "--identity",
            "--tile",
            "--nointratileopt",
            "--noprevector",
            "--nounrolljam",
            "--nodiamond-tile",
            "--noparallel",
        ]
        successes = 0
        both_failed = 0
        for fixture in fixtures:
            noiss = self.run_polopt(
                "identity-iss-sensitive-search", fixture.stem, [fixture], base_args
            )
            iss = self.run_polopt(
                "identity-iss-sensitive-search",
                fixture.stem,
                [fixture],
                [*base_args, "--iss"],
            )
            noiss_output = optimized_loop(noiss.stdout)
            iss_output = optimized_loop(iss.stdout)
            if noiss.returncode == 0 and iss.returncode == 0 and noiss_output and iss_output:
                self.add_pair(
                    "identity-iss-sensitive-search",
                    fixture.stem,
                    noiss_output,
                    iss_output,
                    left_label="Identity Tiling without ISS",
                    right_label="Identity Tiling with ISS",
                    command=["./polopt", *base_args, "[--iss]", fixture.name],
                    note="This search compares two accepted outputs; it is not a source-to-target compilation count.",
                )
                successes += 1
            elif noiss.returncode != 0 and iss.returncode != 0:
                both_failed += 1
            else:
                self.failures.append(
                    f"identity-iss-sensitive-search/{fixture.stem}: unexpected asymmetric result "
                    f"noiss={noiss.returncode}, iss={iss.returncode}"
                )
        require(successes == 42, f"expected 42 identity ISS pairs, got {successes}")
        require(both_failed == 29, f"expected 29 identity ISS paired failures, got {both_failed}")
        print("[identity-iss-sensitive-search] collected 42; both failed 29", flush=True)

    def collect_pluto_compat(self) -> None:
        module_dir = self.source / "tools/polopt_flag_suites"
        sys.path.insert(0, str(module_dir))
        module = load_module(
            "program_views_pluto_compat", module_dir / "run_pluto_compat_suite.py"
        )
        checks = module.active_checks()
        accepted = [check for check in checks if check.success]
        require(len(accepted) == 147, f"expected 147 driver outputs, got {len(accepted)}")
        for check in accepted:
            control_target = module.explicit_control_target(check.explicit_control_flag)
            try:
                if check.explicit_control_flag:
                    with tempfile.TemporaryDirectory(prefix="polcert-program-control-") as tmp:
                        control = Path(tmp) / "control.in"
                        control.write_text(check.explicit_control_file_content, encoding="utf-8")
                        proc = module.run_polopt_compat(
                            [*check.args, check.explicit_control_flag, str(control)],
                            check.fixture,
                            self.timeout,
                            env_extra=check.env,
                            native=check.native,
                        )
                elif check.implicit_control_file:
                    with tempfile.TemporaryDirectory(prefix="polcert-program-implicit-") as tmp:
                        cwd = Path(tmp)
                        (cwd / check.implicit_control_file).write_text(
                            check.implicit_control_file_content, encoding="utf-8"
                        )
                        proc = module.run_polopt_compat(
                            check.args,
                            check.fixture,
                            self.timeout,
                            cwd=cwd,
                            env_extra=check.env,
                            native=check.native,
                        )
                else:
                    proc = module.run_polopt_compat(
                        check.args,
                        check.fixture,
                        self.timeout,
                        env_extra=check.env,
                        native=check.native,
                    )
            except subprocess.TimeoutExpired:
                self.failures.append(f"driver option configurations/{check.name}: timed out")
                continue
            after = optimized_loop(proc.stdout)
            if proc.returncode != 0 or after is None:
                self.failures.append(
                    f"driver option configurations/{check.name}: exit={proc.returncode}, "
                    f"optimized={after is not None}\nstderr:\n{proc.stderr[-2000:]}"
                )
                continue
            mode = [] if check.native else ["--pluto-compat", "--explain"]
            public_args = [*mode, *check.args]
            if check.explicit_control_flag:
                public_args.extend([check.explicit_control_flag, "<control-file>"])
            self.add_pair(
                "driver option configurations",
                check.name,
                check.fixture.read_text(encoding="utf-8"),
                after,
                command=["./polopt", *public_args, check.fixture.name],
            )
            require(
                control_target is None or not (self.source / control_target).exists(),
                f"driver check left control file {control_target}",
            )
        print("[driver option configurations] collected 147", flush=True)

    def collect_second_level_diamond(self) -> None:
        fixture = self.source / "tools/parallel_current/fixtures/diamond-example-inner-batch.loop"
        tile_modes = ("--diamond-tile", "--full-diamond-tile")
        consumers = (
            ("parallel-current", ("--parallel-current", "0")),
            ("parallel-strict", ("--parallel", "--parallel-strict")),
            ("vector-strict", ("--vector", "--vector-strict")),
            (
                "multipar-strict",
                (
                    "--tile",
                    "--smartfuse",
                    "--nointratileopt",
                    "--noprevector",
                    "--nounrolljam",
                    "--rar",
                    "--parallel",
                    "--multipar",
                    "--innerpar",
                    "--parallel-strict",
                ),
            ),
        )
        count = 0
        for tile_mode in tile_modes:
            for consumer, consumer_args in consumers:
                for use_iss in (False, True):
                    case = "-".join(
                        f"second-level {tile_mode} {consumer}{' ISS' if use_iss else ''}"
                        .replace("--", "")
                        .split()
                    )
                    args = ["--second-level-tile", tile_mode, *consumer_args]
                    if use_iss:
                        args.append("--iss")
                    self.collect_loop_command(
                        "two-level tiling route checks", case, [fixture], args
                    )
                    count += 1
        require(count == 16, f"expected 16 second-level diamond outputs, got {count}")
        print("[two-level tiling route checks] collected 16", flush=True)

    def collect_standalone_second_level(self) -> None:
        module = load_module(
            "program_views_standalone_second_level",
            self.source
            / "tools/second_level_tiling/check_standalone_formal_route.py",
        )
        pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
        require(pluto.is_file(), f"missing fixed Pluto: {pluto}")
        fixture = (
            self.source
            / "tools/second_level_tiling/fixtures/symbolic-independent-2d.loop"
        )

        with tempfile.TemporaryDirectory(prefix="polcert-standalone-view-") as tmp:
            work = Path(tmp)
            extracted = self.run_polopt(
                "two-level tiling route checks",
                "standalone-extraction",
                [fixture],
                ["--extract-only"],
                cwd=work,
            )
            require(
                extracted.returncode == 0,
                f"standalone extraction failed:\n{extracted.stderr[-2000:]}",
            )
            source = work / "source.scop"
            source.write_text(extracted.stdout, encoding="utf-8")

            def pluto_phase(input_scop: Path, flags: list[str], label: str) -> Path:
                proc = subprocess.run(
                    [str(pluto), *flags, input_scop.name],
                    cwd=work,
                    env=self.env,
                    text=True,
                    capture_output=True,
                    timeout=self.timeout,
                    check=False,
                )
                output = input_scop.with_name(
                    f"{input_scop.name}.afterscheduling.scop"
                )
                require(
                    proc.returncode == 0 and output.is_file(),
                    f"{label} failed: exit={proc.returncode}\n{proc.stderr[-2000:]}",
                )
                return output

            affine = pluto_phase(
                source,
                list(module.AFFINE_PLUTO_FLAGS),
                "standalone affine midpoint",
            )
            midpoint = work / "midpoint.scop"
            midpoint.write_bytes(affine.read_bytes())
            posttile = pluto_phase(
                midpoint,
                list(module.TILING_PLUTO_FLAGS),
                "phase-aligned two-level tiling",
            )
            direct_source = work / "direct-source.scop"
            direct_source.write_text(extracted.stdout, encoding="utf-8")
            direct_posttile = pluto_phase(
                direct_source,
                list(module.TILING_PLUTO_FLAGS),
                "source-like two-level tiling",
            )

            cases = (
                (
                    "phase-aligned-standalone-formal-tiling-validation",
                    midpoint,
                    posttile,
                ),
                (
                    "source-like-standalone-formal-band-validation",
                    direct_source,
                    direct_posttile,
                ),
            )
            for case, before, after in cases:
                checked = self.run_polopt(
                    "two-level tiling route checks",
                    case,
                    [before, after],
                    ["--second-level-tile", "--validate-tiling-openscop"],
                    cwd=work,
                )
                require(
                    checked.returncode == 0
                    and "overall: PASS" in checked.stdout
                    and "formal: PASS" in checked.stdout
                    and checked.stderr.count(module.BAND_ROUTE) == 1,
                    f"standalone two-level pair did not validate: {case}\n"
                    f"stdout:\n{checked.stdout[-2000:]}\n"
                    f"stderr:\n{checked.stderr[-2000:]}",
                )
                self.add_pair(
                    "two-level tiling route checks",
                    case,
                    before.read_text(encoding="utf-8"),
                    after.read_text(encoding="utf-8"),
                    left_label="Before Two-Level Tiling SCoP",
                    right_label="Accepted Two-Level Tiled SCoP",
                    extension="scop",
                    command=[
                        "./polopt",
                        "--second-level-tile",
                        "--validate-tiling-openscop",
                        before.name,
                        after.name,
                    ],
                )
        print("[two-level tiling route checks] collected 2 standalone pairs", flush=True)

    def collect_direct_routes(self) -> None:
        symbolic = self.source / "tools/second_level_tiling/fixtures/symbolic-independent-2d.loop"
        mixed = self.source / "tools/second_level_tiling/fixtures/matmul-init.loop"
        dependent = self.source / "tools/parallel_current/fixtures/dependent.loop"
        cases = (
            ("ordinary-common-band", symbolic, []),
            ("second-level-zero-row-band", symbolic, ["--second-level-tile"]),
            ("second-level-zero-row-band-iss", symbolic, ["--second-level-tile", "--iss"]),
            ("ordinary-phase-separated-mixed-depth", mixed, []),
            ("ordinary-phase-separated-mixed-depth-iss", mixed, ["--iss"]),
            ("mixed-depth-semantic-band", mixed, ["--identity-tiled"]),
            ("mixed-depth-semantic-band-iss", mixed, ["--identity-tiled", "--iss"]),
            (
                "second-level-mixed-depth-semantic-band",
                mixed,
                ["--second-level-tile", "--identity-tiled"],
            ),
            (
                "second-level-mixed-depth-semantic-band-iss",
                mixed,
                ["--second-level-tile", "--identity-tiled", "--iss"],
            ),
            ("dependent-one-dimensional-band", dependent, []),
        )
        for case, fixture, args in cases:
            self.collect_loop_command(
                "direct tiling-validator routes", case, [fixture], args
            )
        print("[direct tiling-validator routes] collected 10", flush=True)

    def collect_end_to_end_c(self) -> None:
        root = self.source / "tests/end-to-end-c/cases"
        cases = (
            ("matmul [sequential]", root / "matmul/matmul.loop", [], {}),
            (
                "matmul [parallel]",
                root / "matmul/matmul.loop",
                ["--parallel"],
                {},
            ),
            (
                "matmul [innermost-parallel]",
                root / "matmul/matmul.loop",
                ["--rar", "--vector-current", "5"],
                {},
            ),
            (
                "parallel_const_unroll",
                root / "parallel_const_unroll/parallel_const_unroll.loop",
                ["--identity", "--const-unroll", "--parallel-current", "0"],
                {},
            ),
            (
                "reverse_iss",
                root / "reverse_iss/reverse_iss.loop",
                ["--iss"],
                {},
            ),
        )
        for case, fixture, args, env in cases:
            self.collect_loop_command(
                "handwritten C execution", case, [fixture], args, env=env
            )
        print("[handwritten C execution] collected 5", flush=True)

    def collect_generated_effects(self) -> None:
        root = self.source / "tests/polopt-generated/inputs"
        specs = (
            (
                "generated execution: parallel-effect",
                "corcol3",
                ["--parallel"],
            ),
            (
                "generated execution: parallel-effect",
                "doitgen",
                ["--parallel"],
            ),
            (
                "generated execution: parallel-effect",
                "matmul",
                ["--parallel"],
            ),
            (
                "generated execution: second-level-effect",
                "matmul-init",
                ["--second-level-tile"],
            ),
            (
                "generated execution: intratile-effect",
                "matmul",
                ["--intratileopt"],
            ),
        )
        for suite, case, args in specs:
            self.collect_loop_command(suite, case, [root / f"{case}.loop"], args)
        print("[generated execution effects] collected 5", flush=True)

    def collect_legacy_programs(self) -> None:
        def build_test(relative: str, timeout: int = 1800) -> Path:
            directory = self.source / relative
            proc = subprocess.run(
                ["opam", "exec", "--switch=polcert", "--", "make", "-C", str(directory)],
                cwd=self.source,
                env=self.env,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
            executable = directory / "test"
            require(
                proc.returncode == 0 and executable.is_file(),
                f"legacy test failed in {relative}: exit={proc.returncode}\n"
                f"stdout:\n{proc.stdout[-4000:]}\nstderr:\n{proc.stderr[-4000:]}",
            )
            return directory

        affine_root = build_test("tests/pluto-all")
        affine_cases = sorted(
            path.stem
            for path in (self.source / "tests/polopt-generated/inputs").glob("*.loop")
        )
        require(len(affine_cases) == 62, f"expected 62 affine cases, got {len(affine_cases)}")
        for case in affine_cases:
            self.add_pair(
                "affine schedule refinement",
                case,
                (affine_root / case / "in.scop").read_text(encoding="utf-8"),
                (affine_root / case / "out.scop").read_text(encoding="utf-8"),
                left_label="Before-Scheduling OpenScop Program",
                right_label="Accepted Scheduled OpenScop Program",
                extension="scop",
                command=["tests/pluto-all/test"],
                note=(
                    "These are the exact OpenScop objects compared by the legacy "
                    "mutual-refinement test."
                ),
            )

        readscop_root = build_test("tests/readscop")
        for stem in (".afterscheduling", ".beforescheduling", ".simple"):
            before = readscop_root / "scops" / stem
            after = before.with_name(before.name + ".output")
            after_again = after.with_name(after.name + ".output")
            for case, left, right in (
                (f"./scops/{stem}", before, after),
                (f"./scops/{stem}.output", after, after_again),
            ):
                self.add_pair(
                    "OpenScop round trips",
                    case,
                    left.read_text(encoding="utf-8"),
                    right.read_text(encoding="utf-8"),
                    left_label="OpenScop Input",
                    right_label="Reprinted OpenScop Program",
                    extension="scop",
                    command=["tests/readscop/test", case],
                )

        cpol_root = build_test("tests/cpol2copenscop")
        self.add_pair(
            "CPoly-to-OpenScop conversion",
            "both-conversions",
            (cpol_root / "1_cpol.output").read_text(encoding="utf-8"),
            (cpol_root / "3_cpol.output").read_text(encoding="utf-8"),
            left_label="Input CPoly Program",
            right_label="CPoly Program After OpenScop Round Trip",
            extension="cpol",
            command=["tests/cpol2copenscop/test"],
            note=(
                "This smoke test checks that both conversions succeed; it does "
                "not claim structural equality of the two printed programs."
            ),
        )

        scheduler_root = build_test("tests/pluto")
        self.add_pair(
            "scheduler conversion smoke test",
            "scheduler-smoke",
            (scheduler_root / "orig.cpol").read_text(encoding="utf-8"),
            (scheduler_root / "opt.cpol").read_text(encoding="utf-8"),
            left_label="Input CPoly Program",
            right_label="Pluto-Scheduled CPoly Program",
            extension="cpol",
            command=["tests/pluto/test"],
        )
        print(
            "[legacy program views] replaced 62 affine and collected 8 conversion pairs",
            flush=True,
        )

    def collect_rejected_pluto_programs(self) -> None:
        polycc = Path(
            os.environ.get("POLCERT_BUGGY_POLYCC", "/opt/polcert/pluto-buggy/polycc")
        )
        require(polycc.is_file(), f"missing pinned buggy polycc: {polycc}")
        root = self.source / "tests/pluto-bugs"
        specs = (
            (
                "affine-fst-reversed",
                "affine_fst_reversed.c",
                [
                    "--dumpscop", "--notile", "--nodiamond-tile",
                    "--nointratileopt", "--noprevector", "--nounrolljam",
                    "--noparallel",
                ],
                (("reversed.fst", ".fst"),),
            ),
            (
                "auto-affine-lp-cc-scaling",
                "auto_affine_lp_cc_scaling.c",
                [
                    "--dumpscop", "--maxfuse", "--lp", "--notile",
                    "--noparallel", "--noprevector", "--nounrolljam",
                    "--nointratileopt", "--nodiamond-tile",
                ],
                (),
            ),
            (
                "tiling-innerpar-satvec",
                "tiling_innerpar_satvec.c",
                [
                    "--dumpscop", "--identity", "--tile", "--parallel",
                    "--innerpar", "--nodiamond-tile", "--nointratileopt",
                    "--noprevector", "--nounrolljam",
                ],
                (("tile.sizes", "tile.sizes"),),
            ),
            (
                "vanished-outer-parallel",
                "vanished_outer_parallel.c",
                [
                    "--notile", "--nodiamond-tile", "--nointratileopt",
                    "--noprevector", "--nounrolljam", "--parallel",
                ],
                (),
            ),
            (
                "notile-unrolljam-nonpermutable",
                "notile_unrolljam_nonpermutable.c",
                [
                    "--identity", "--notile", "--nodiamond-tile",
                    "--nointratileopt", "--noprevector", "--unrolljam",
                    "--ufactor=2", "--noparallel",
                ],
                (),
            ),
        )
        for case, source_name, flags, controls in specs:
            fixture = root / case
            source = fixture / source_name
            with tempfile.TemporaryDirectory(prefix="polcert-rejected-view-") as tmp:
                work = Path(tmp)
                work_source = work / source.name
                shutil.copy2(source, work_source)
                for original, installed in controls:
                    shutil.copy2(fixture / original, work / installed)
                proc = subprocess.run(
                    [str(polycc), *flags, source.name],
                    cwd=work,
                    text=True,
                    capture_output=True,
                    timeout=self.timeout,
                    check=False,
                )
                generated = work / f"{source.stem}.pluto.c"
                require(
                    proc.returncode == 0 and generated.is_file(),
                    f"bug witness no longer produces candidate {case}: "
                    f"exit={proc.returncode}\n{proc.stdout[-2000:]}",
                )
                self.add_pair(
                    "optimizer reliability",
                    case,
                    source.read_text(encoding="utf-8"),
                    generated.read_text(encoding="utf-8"),
                    left_label="Original C Program",
                    right_label="Rejected Pluto-Generated C Program",
                    extension="c",
                    command=["polycc", *flags, source.name],
                    kind="rejected-candidate-pair",
                    note=(
                        "This is the exact generated program from the pinned "
                        "historical Pluto revision used by the rejection test."
                    ),
                )
        print("[optimizer reliability] collected 5", flush=True)

    def collect_diamond_rejection(self) -> None:
        wrapper = Path(
            os.environ.get(
                "POLCERT_CAPTURE_REJECTING_PLUTO",
                str(Path(__file__).resolve().with_name("capture_rejecting_pluto.py")),
            )
        ).resolve()
        pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
        require(wrapper.is_file(), f"missing capture wrapper: {wrapper}")
        require(pluto.is_file(), f"missing fixed Pluto: {pluto}")
        case = "diamond-nointratile-reschedule"
        fixture = self.source / "tests/pluto-bugs" / case / "input.loop"
        args = [
            "--pluto-compat",
            "--tile",
            "--smartfuse",
            "--nointratileopt",
            "--noprevector",
            "--nounrolljam",
            "--rar",
            "--diamond-tile",
            "--noparallel",
            "--tile-sizes-file",
            "tests/pluto-bugs/diamond-nointratile-reschedule/tile.sizes",
        ]
        with tempfile.TemporaryDirectory(prefix="polcert-diamond-rejected-view-") as tmp:
            capture = Path(tmp)
            env = self.env.copy()
            env.update(
                {
                    "POLCERT_PLUTO": str(wrapper),
                    "POLCERT_REJECTING_PLUTO_BASE": str(pluto),
                    "POLCERT_REJECTING_PLUTO_MODE": "tiling",
                    "POLCERT_REJECTING_CAPTURE": str(capture),
                    "POLCERT_REJECTING_CAPTURE_LABEL": case,
                }
            )
            checked = self.run_polopt(
                "optimizer reliability",
                case,
                [fixture],
                args,
                env=env,
                cwd=self.source,
            )
            require(
                checked.returncode == 2
                and optimized_loop(checked.stdout) is None
                and "[tiling-validation] route=rejected" in checked.stderr,
                "diamond mixed-scalar candidate was not rejected as expected:\n"
                + (checked.stdout + checked.stderr)[-4000:],
            )
            candidates = []
            for invocation in sorted((capture / case).glob("*")):
                command_path = invocation / "command.json"
                if not command_path.is_file():
                    continue
                command = json.loads(command_path.read_text(encoding="utf-8"))
                if "--diamond-tile" in command or "--full-diamond-tile" in command:
                    candidates.append(invocation)
            require(
                len(candidates) == 1,
                f"expected one captured diamond tiling proposal, got {len(candidates)}",
            )
            proposal = candidates[0]
            self.add_pair(
                "optimizer reliability",
                case,
                (proposal / "before.scop").read_text(encoding="utf-8"),
                (proposal / "candidate.scop").read_text(encoding="utf-8"),
                left_label="Input Polyhedral Program",
                right_label="Rejected Diamond-Tiling Candidate",
                extension="scop",
                command=["./polopt", *args, fixture.name],
                kind="rejected-candidate-pair",
                note=(
                    "PolCert rejects this mixed-scalar diamond proposal before "
                    "code generation; no target Loop program is emitted."
                ),
            )
        print("[optimizer reliability] collected diamond candidate", flush=True)

    def collect_live_iss_rejection(self) -> None:
        module = load_module(
            "program_views_live_iss",
            self.source / "tools/iss/run_pluto_iss_live_suite.py",
        )
        source = Path("/pluto/test/jacobi-2d-periodic.c")
        require(source.is_file(), f"missing live ISS source: {source}")
        with tempfile.TemporaryDirectory(prefix="polcert-live-iss-view-") as tmp:
            work = Path(tmp)
            valid = work / "valid.bridge"
            invalid = work / "bad_cut.bridge"
            code, output = module.emit_pluto_bridge(source, valid)
            require(
                code == 0 and valid.is_file(),
                f"live ISS bridge emission failed: exit={code}\n{output[-2000:]}",
            )
            module.mutate_bad_cut(valid, invalid)
            checked = self.run_polopt(
                "ISS from live Pluto output",
                "mutated-cut",
                [invalid],
                ["--validate-iss-bridge"],
            )
            combined = checked.stdout + "\n" + checked.stderr
            require(
                checked.returncode == 1 and "validation: FAIL" in combined,
                "mutated live ISS bridge was not rejected:\n" + combined[-3000:],
            )
            self.add_pair(
                "ISS from live Pluto output",
                "mutated-cut",
                valid.read_text(encoding="utf-8"),
                invalid.read_text(encoding="utf-8"),
                left_label="Original ISS Proposal",
                right_label="Rejected Mutated ISS Proposal",
                extension="bridge",
                command=["./polopt", "--validate-iss-bridge", "bad_cut.bridge"],
                kind="rejected-candidate-pair",
                note=(
                    "The candidate differs by one corrupted cut constant; the "
                    "ISS validator rejects it."
                ),
            )
        print("[ISS from live Pluto output] collected mutated candidate", flush=True)

    def collect_rejected_tiling_candidates(self) -> None:
        module = load_module(
            "program_views_rejected_tiling",
            self.source
            / "tools/second_level_tiling/check_rejected_tiling_route.py",
        )
        wrapper = Path(
            os.environ.get(
                "POLCERT_CAPTURE_REJECTING_PLUTO",
                str(Path(__file__).resolve().with_name("capture_rejecting_pluto.py")),
            )
        ).resolve()
        base = self.source / "tools/second_level_tiling/rejecting_pluto.py"
        real_pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
        require(wrapper.is_file(), f"missing capture wrapper: {wrapper}")
        require(base.is_file(), f"missing rejecting Pluto wrapper: {base}")
        require(real_pluto.is_file(), f"missing fixed Pluto: {real_pluto}")

        with tempfile.TemporaryDirectory(prefix="polcert-rejected-tiling-views-") as tmp:
            capture = Path(tmp)

            def run_case(
                case: str,
                fixture: Path,
                args: tuple[str, ...],
                mode: str,
            ) -> None:
                env = self.env.copy()
                env.update(
                    {
                        "POLCERT_REAL_PLUTO": str(real_pluto),
                        "POLCERT_PLUTO": str(wrapper),
                        "POLCERT_REJECTING_PLUTO_BASE": str(base),
                        "POLCERT_REJECTING_PLUTO_MODE": mode,
                        "POLCERT_REJECTING_CAPTURE": str(capture),
                        "POLCERT_REJECTING_CAPTURE_LABEL": case,
                    }
                )
                proc = self.run_polopt(
                    "second-level rejection",
                    case,
                    [fixture],
                    list(args),
                    env=env,
                )
                require(
                    proc.returncode != 0 and optimized_loop(proc.stdout) is None,
                    f"expected rejected tiling case: {case}",
                )
                captures = sorted((capture / case).glob("*/before.scop"))
                candidates = sorted((capture / case).glob("*/candidate.scop"))
                require(
                    captures and len(captures) == len(candidates),
                    f"missing phase captures for {case}",
                )

                def bundle(paths: list[Path]) -> str:
                    if len(paths) == 1:
                        return paths[0].read_text(encoding="utf-8")
                    chunks = []
                    for index, path in enumerate(paths, 1):
                        chunks.append(
                            f"# Phase proposal {index}\n"
                            + path.read_text(encoding="utf-8").rstrip()
                        )
                    return "\n\n".join(chunks) + "\n"

                self.add_pair(
                    "second-level rejection",
                    case,
                    bundle(captures),
                    bundle(candidates),
                    left_label="Input Polyhedral Program",
                    right_label="Rejected Polyhedral Candidate",
                    extension="scop",
                    command=["./polopt", *args, fixture.name],
                    kind="rejected-candidate-pair",
                )

            malformed = {
                case.name: case for case in module.malformed_tiling_cases(self.source)
            }
            for name, case in malformed.items():
                run_case(f"malformed-{name}", case.fixture, case.args, "tiling")

            explicit_producers = (
                "ordinary",
                "identity-mixed-depth-iss",
                "second-level",
                "second-level-identity-mixed-depth-iss",
                "diamond",
                "full-diamond-iss",
                "second-level-diamond",
                "second-level-full-diamond-iss",
            )
            for producer_name in explicit_producers:
                producer = malformed[producer_name]
                for consumer_name, consumer_args in (
                    ("parallel-current", ("--parallel-current", "999")),
                    ("vector-current", ("--vector-current", "999")),
                ):
                    run_case(
                        f"malformed-{producer_name}-with-{consumer_name}",
                        producer.fixture,
                        (*producer.args, *consumer_args),
                        "tiling",
                    )

            hinted_consumers = (
                (
                    "parallel",
                    (
                        "--parallel", "--innerpar", "--smartfuse",
                        "--nointratileopt", "--noprevector", "--nounrolljam",
                        "--rar",
                    ),
                ),
                (
                    "parallel-strict",
                    (
                        "--parallel", "--parallel-strict", "--innerpar",
                        "--smartfuse", "--nointratileopt", "--noprevector",
                        "--nounrolljam", "--rar",
                    ),
                ),
                (
                    "multipar",
                    (
                        "--parallel", "--multipar", "--innerpar",
                        "--smartfuse", "--nointratileopt", "--noprevector",
                        "--nounrolljam", "--rar",
                    ),
                ),
                (
                    "multipar-strict",
                    (
                        "--parallel", "--multipar", "--parallel-strict",
                        "--innerpar", "--smartfuse", "--nointratileopt",
                        "--noprevector", "--nounrolljam", "--rar",
                    ),
                ),
                (
                    "vector",
                    (
                        "--vector", "--smartfuse", "--nointratileopt",
                        "--nounrolljam", "--rar", "--noparallel",
                    ),
                ),
                (
                    "vector-strict",
                    (
                        "--vector", "--vector-strict", "--smartfuse",
                        "--nointratileopt", "--nounrolljam", "--rar",
                        "--noparallel",
                    ),
                ),
            )
            for producer_name in (
                "ordinary", "diamond", "second-level-full-diamond-iss"
            ):
                producer = malformed[producer_name]
                explicit_phase = (
                    ()
                    if any(
                        flag in producer.args
                        for flag in ("--diamond-tile", "--full-diamond-tile")
                    )
                    else ("--nodiamond-tile",)
                )
                for consumer_name, consumer_args in hinted_consumers:
                    run_case(
                        f"malformed-{producer_name}-with-hinted-{consumer_name}",
                        producer.fixture,
                        (*producer.args, *consumer_args, *explicit_phase),
                        "tiling",
                    )

            diamond = (
                self.source
                / "tools/parallel_current/fixtures/diamond-example-inner-batch.loop"
            )
            final_producers = (
                ("diamond", ("--diamond-tile",)),
                ("diamond-iss", ("--diamond-tile", "--iss")),
                ("full-diamond", ("--full-diamond-tile",)),
                ("full-diamond-iss", ("--full-diamond-tile", "--iss")),
                (
                    "second-level-diamond",
                    ("--second-level-tile", "--diamond-tile"),
                ),
                (
                    "second-level-diamond-iss",
                    ("--second-level-tile", "--diamond-tile", "--iss"),
                ),
                (
                    "second-level-full-diamond",
                    ("--second-level-tile", "--full-diamond-tile"),
                ),
                (
                    "second-level-full-diamond-iss",
                    ("--second-level-tile", "--full-diamond-tile", "--iss"),
                ),
            )
            final_consumers = (
                ("sequential", ()),
                ("parallel-current", ("--parallel-current", "0")),
                ("vector-current", ("--vector-current", "0")),
                (
                    "parallel-hint-strict",
                    (
                        "--parallel", "--parallel-strict", "--innerpar",
                        "--smartfuse", "--nointratileopt", "--noprevector",
                        "--nounrolljam", "--rar",
                    ),
                ),
                (
                    "multipar-hint-strict",
                    (
                        "--parallel", "--multipar", "--parallel-strict",
                        "--innerpar", "--smartfuse", "--nointratileopt",
                        "--noprevector", "--nounrolljam", "--rar",
                    ),
                ),
                (
                    "vector-hint-strict",
                    (
                        "--vector", "--vector-strict", "--smartfuse",
                        "--nointratileopt", "--nounrolljam", "--rar",
                        "--noparallel",
                    ),
                ),
            )
            for producer_name, producer_args in final_producers:
                for consumer_name, consumer_args in final_consumers:
                    run_case(
                        f"final-affine-{producer_name}-with-{consumer_name}",
                        diamond,
                        (*producer_args, *consumer_args),
                        "final-affine",
                    )
        print("[second-level rejection] collected 98", flush=True)

    def collect_rejected_fixture_candidates(self) -> None:
        tiling = load_module(
            "program_views_scalar_tiling",
            self.source / "tools/tiling_routes/check_scalar_interleaved_fusion.py",
        )
        posttile = self.source / "tools/tiling_routes/fixtures/fusion5-scalar-interleaved.posttile.scop"
        midpoint = self.source / "tools/tiling_routes/fixtures/fusion5-scalar-interleaved.midtransform.scop"
        source_lines = posttile.read_text(encoding="utf-8").splitlines()
        mutations = (
            ("scalar-row-deleted", tiling.mutate_scalar_deletion(source_lines)),
            ("scalar-row-reordered", tiling.mutate_scalar_position(source_lines)),
            ("scalar-constant-changed", tiling.mutate_scalar_constant(source_lines)),
            (
                "noncanonical-output-matrix",
                tiling.mutate_noncanonical_output_matrix(source_lines),
            ),
        )
        for case, lines in mutations:
            self.add_pair(
                "scalar-interleaved tiling",
                case,
                midpoint.read_text(encoding="utf-8"),
                "\n".join(lines) + "\n",
                left_label="Input Polyhedral Program",
                right_label="Rejected Tiling Candidate",
                extension="scop",
                kind="rejected-candidate-pair",
            )

        iss = load_module(
            "program_views_iss_rejections",
            self.source / "tools/iss/run_pluto_iss_suite.py",
        )
        iss_data = self.source / "tests/iss-pluto-dumps"
        with tempfile.TemporaryDirectory(prefix="polcert-iss-rejected-views-") as tmp:
            tmp_path = Path(tmp)
            bad_halfspace = tmp_path / "reverse_bad_halfspace.txt"
            bad_payload = tmp_path / "reverse_bad_payload.txt"
            iss.mutate_bad_halfspace(iss_data / "reverse_after.txt", bad_halfspace)
            iss.mutate_bad_payload(iss_data / "reverse_after.txt", bad_payload)
            for case, candidate in (
                ("iss-name-collision", iss_data / "iss_name_collision.txt"),
                ("reverse_bad_halfspace", bad_halfspace),
                ("reverse_bad_payload", bad_payload),
            ):
                self.add_pair(
                    "ISS validator",
                    case,
                    (iss_data / "reverse_before.txt").read_text(encoding="utf-8"),
                    candidate.read_text(encoding="utf-8"),
                    left_label="Before ISS Program",
                    right_label="Rejected ISS Candidate",
                    extension="txt",
                    kind="rejected-candidate-pair",
                )

        fixtures = self.source / "tools/tiling_routes/fixtures"
        self.add_pair(
            "second-level rejection",
            "nonpermutable-band",
            (fixtures / "nonpermutable-band.midtransform.scop").read_text(
                encoding="utf-8"
            ),
            (fixtures / "nonpermutable-band.posttile.scop").read_text(
                encoding="utf-8"
            ),
            left_label="Input Polyhedral Program",
            right_label="Rejected Non-Permutable Candidate",
            extension="scop",
            kind="rejected-candidate-pair",
        )
        strict_fixture = self.source / "tools/second_level_tiling/fixtures/matmul-init.loop"
        for second_level in (False, True):
            for use_iss in (False, True):
                case = (
                    ("second-level-" if second_level else "")
                    + "identity-vector-strict"
                    + ("-iss" if use_iss else "")
                )
                args = ["--identity", "--tile"]
                if second_level:
                    args.append("--second-level-tile")
                if use_iss:
                    args.append("--iss")
                args.extend(
                    [
                        "--vector", "--vector-strict", "--nointratileopt",
                        "--nounrolljam", "--nodiamond-tile", "--noparallel",
                    ]
                )
                self.collect_loop_command(
                    "second-level rejection", case, [strict_fixture], args
                )
        print(
            "[rejected fixture candidates] collected 8 rejected and 4 accepted",
            flush=True,
        )

    def finish(self) -> None:
        if self.failures:
            raise RuntimeError(
                "program comparison collection failed:\n" + "\n".join(self.failures)
            )
        records = sorted(
            self.records.values(), key=lambda item: (str(item["suite"]), str(item["case"]))
        )
        (self.output / "index.json").write_text(
            json.dumps(
                {
                    "producer": {
                        "polopt_sha256": self.polopt_sha256,
                        "fixed_pluto_sha256": self.pluto_sha256,
                        "historical_polycc_sha256": self.buggy_polycc_sha256,
                    },
                    "pairs": records,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        print(f"wrote {len(records)} program pairs to {self.output}", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument(
        "--expected-polopt-sha256",
        default=FROZEN_POLOPT_SHA256,
        help="exact frozen Release binary required for evidence collection",
    )
    parser.add_argument(
        "--families",
        default=(
            "manifests,one-level,identity-iss,driver,"
            "second-level-diamond,standalone-second-level,direct,end-to-end-c,"
            "generated-effects,rejected-pluto,diamond-rejection,live-iss-rejection,"
            "rejected-tiling,rejected-fixtures,legacy-programs"
        ),
        help="comma-separated collector families",
    )
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--append", action="store_true")
    parser.add_argument("--replace-existing", action="store_true")
    args = parser.parse_args()

    require(not (args.force and args.append), "--force and --append are exclusive")
    require(
        not args.replace_existing or args.append,
        "--replace-existing requires --append",
    )
    if args.output.exists() and args.force:
        shutil.rmtree(args.output)
    if not args.append:
        require(not args.output.exists(), f"output already exists: {args.output}")
    require((args.source / "polopt").is_file(), f"missing polopt in {args.source}")

    collector = Collector(
        args.source,
        args.output,
        args.timeout,
        args.expected_polopt_sha256,
        args.replace_existing,
    )
    if args.append:
        collector.load_existing()
    actions = {
        "manifests": collector.collect_manifests,
        "one-level": collector.collect_one_level,
        "identity-iss": collector.collect_identity_iss,
        "driver": collector.collect_pluto_compat,
        "second-level-diamond": collector.collect_second_level_diamond,
        "standalone-second-level": collector.collect_standalone_second_level,
        "direct": collector.collect_direct_routes,
        "end-to-end-c": collector.collect_end_to_end_c,
        "generated-effects": collector.collect_generated_effects,
        "legacy-programs": collector.collect_legacy_programs,
        "rejected-pluto": collector.collect_rejected_pluto_programs,
        "diamond-rejection": collector.collect_diamond_rejection,
        "live-iss-rejection": collector.collect_live_iss_rejection,
        "rejected-tiling": collector.collect_rejected_tiling_candidates,
        "rejected-fixtures": collector.collect_rejected_fixture_candidates,
    }
    families = [name for name in args.families.split(",") if name]
    unknown = sorted(set(families) - set(actions))
    require(not unknown, "unknown families: " + ", ".join(unknown))
    for family in families:
        actions[family]()
    collector.finish()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
