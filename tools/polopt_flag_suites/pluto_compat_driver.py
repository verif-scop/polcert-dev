#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_POLOPT = ROOT / "polopt"


class Reject(Exception):
    pass


@dataclass(frozen=True)
class WrapperConfig:
    polopt: Path
    dry_run: bool
    explain: bool
    timeout: float | None


@dataclass
class PlutoFlagState:
    input_path: Path
    tile: bool = True
    tile_seen: bool = False
    notile_seen: bool = False
    identity: bool = False
    iss: bool = False
    second_level_tile: bool = False
    diamond_tile: bool = False
    diamond_seen: bool = False
    nodiamond_seen: bool = False
    full_diamond_tile: bool = False
    parallel: bool = False
    parallel_seen: bool = False
    innerpar_seen: bool = False
    no_parallel_seen: bool = False
    no_intratileopt_seen: bool = False
    no_prevector_seen: bool = False
    no_unrolljam_seen: bool = False
    notes: list[str] | None = None

    def add_note(self, msg: str) -> None:
        if self.notes is None:
            self.notes = []
        self.notes.append(msg)


VALUE_OPTIONS = {
    "--cache-size",
    "--cloogf",
    "--cloogl",
    "--codegen-context",
    "--coeff-bound",
    "--data-element-size",
    "--forceparallel",
    "--ft",
    "--lt",
    "--ufactor",
    "-o",
}

FRONTEND_OPTIONS = {
    "--pet": "frontend is polopt's verified loop extractor, not Pluto/PET",
    "--readscop": "frontend is polopt's verified loop extractor, not Pluto OpenScop input",
    "--dumpscop": "Pluto OpenScop dumps are an oracle-debug interface, not a polopt input/output mode",
}

META_OPTIONS = {
    "--help": "CLI help is outside the optimizer-compatibility surface",
    "--version": "CLI version reporting is outside the optimizer-compatibility surface",
}

DEPENDENCE_SOLVER_OPTIONS = {
    "--candldep": "Candl dependence testing is not exposed through the checked polopt route",
    "--isldepaccesswise": "ISL dependence-analysis tuning is not exposed through the checked polopt route",
    "--isldepstmtwise": "ISL dependence-analysis tuning is not exposed through the checked polopt route",
    "--isldepcoalesce": "ISL dependence-analysis tuning is not exposed through the checked polopt route",
    "--lastwriter": "last-writer dependence mode is not exposed through the checked polopt route",
    "--nolastwriter": "last-writer dependence mode is not exposed through the checked polopt route",
    "--pipsolve": "PIP solver selection is not exposed through the checked polopt route",
    "--scalpriv": "Candl scalar privatization is not exposed through the checked polopt route",
}

DFP_OPTIONS = {
    "--clusterscc": "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists",
    "--delayedcut": "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists",
    "--dfp": "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists",
    "--glpk": "current Pluto build has no GLPK support and polopt has no checked DFP route",
    "--gurobi": "current Pluto build has no Gurobi support and polopt has no checked DFP route",
    "--hybridfuse": "hybrid fusion depends on DFP/typed fusion, which is outside the checked polopt route",
    "--ilp": "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists",
    "--lp": "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists",
    "--lpcolor": "DFP/typed-fusion options require a Pluto LP build and no checked polopt route exists",
    "--typedfuse": "typed fusion depends on DFP, which is outside the checked polopt route",
}

CODEGEN_OPTIONS = {
    "--bee": "Bee pragmas are Pluto codegen output, while polopt uses its own codegen",
    "--cloogsh": "Cloog codegen tuning is outside the polopt checked route",
    "--indent": "formatting is outside the optimizer-validation route",
    "--prevector": "prevectorization is a Pluto codegen/post-transform effect, while polopt uses its own codegen",
    "--unrolljam": "unroll-jam is a Pluto post-codegen transform, not a checked polopt schedule route",
}

UNSUPPORTED_OPTIMIZER_OPTIONS = {
    "--determine-tile-size": "automatic Pluto tile-size selection is not exposed through the checked polopt route",
    "--fast-lin-ind-check": "fast linear-independence search tuning is not exposed through the checked polopt route",
    "--flic": "fast linear-independence search tuning is not exposed through the checked polopt route",
    "--forceparallel": "Pluto accepts this flag, but the current source has no effective use site",
    "--intratileopt": "Pluto intra-tile schedule rewriting is not exposed through the checked polopt route",
    "--maxfuse": "maximal fusion is not exposed as a checked polopt route",
    "--multipar": "multi-degree Pluto parallel extraction is not exposed through the checked polopt route",
    "--nofuse": "no-fusion scheduling is not exposed as a checked polopt route",
    "--nodepbound": "dependence-bound search tuning is not exposed through the checked polopt route",
    "--per-cc-obj": "per-connected-component objective is not exposed as a checked polopt route",
}

STALE_OR_NON_PLUTO_OPTIONS = {
    "--dump-iss-bridge": "this flag is not accepted by the current Pluto binary",
    "--lbtile": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
    "--multipipe": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
    "--output": "the current Pluto binary uses -o, not --output",
    "--sched": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
    "--variables_not_global": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
}

ACCEPTED_NOOPS = {
    "--debug",
    "--isldep",
    "--islsolve",
    "--moredebug",
    "--nocloogbacktrack",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--rar",
    "--silent",
    "--smartfuse",
}


def usage() -> str:
    return (
        "Usage: pluto_compat_driver.py [--polopt PATH] [--dry-run] [--explain] "
        "[--timeout SECONDS] <pluto-like flags> <file.loop>"
    )


def parse_wrapper_args(argv: list[str]) -> tuple[WrapperConfig, list[str]]:
    polopt = DEFAULT_POLOPT
    dry_run = False
    explain = False
    timeout: float | None = None
    rest: list[str] = []
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--polopt":
            i += 1
            if i >= len(argv):
                raise Reject("--polopt requires a path")
            polopt = Path(argv[i])
        elif arg.startswith("--polopt="):
            polopt = Path(arg.split("=", 1)[1])
        elif arg == "--dry-run":
            dry_run = True
        elif arg == "--explain":
            explain = True
        elif arg == "--timeout":
            i += 1
            if i >= len(argv):
                raise Reject("--timeout requires seconds")
            timeout = float(argv[i])
        elif arg.startswith("--timeout="):
            timeout = float(arg.split("=", 1)[1])
        elif arg == "--":
            rest.extend(argv[i + 1 :])
            break
        else:
            rest.append(arg)
        i += 1

    return WrapperConfig(polopt=polopt, dry_run=dry_run, explain=explain, timeout=timeout), rest


def split_flags_and_input(args: list[str]) -> tuple[list[tuple[str, str | None]], Path]:
    if not args:
        raise Reject(usage())
    input_arg = args[-1]
    if input_arg.startswith("-"):
        raise Reject("missing input .loop file")
    raw_flags = args[:-1]
    flags: list[tuple[str, str | None]] = []
    i = 0
    while i < len(raw_flags):
        flag = raw_flags[i]
        if flag in VALUE_OPTIONS:
            i += 1
            if i >= len(raw_flags):
                raise Reject(f"{flag} requires a value")
            flags.append((flag, raw_flags[i]))
        elif any(flag.startswith(prefix + "=") for prefix in VALUE_OPTIONS):
            prefix, value = flag.split("=", 1)
            flags.append((prefix, value))
        else:
            flags.append((flag, None))
        i += 1
    return flags, Path(input_arg)


def reject_known_flag(flag: str) -> str | None:
    for table in (
        FRONTEND_OPTIONS,
        META_OPTIONS,
        DEPENDENCE_SOLVER_OPTIONS,
        DFP_OPTIONS,
        CODEGEN_OPTIONS,
        UNSUPPORTED_OPTIMIZER_OPTIONS,
        STALE_OR_NON_PLUTO_OPTIONS,
    ):
        if flag in table:
            return table[flag]
    return None


def normalize_pluto_flags(flags: list[tuple[str, str | None]], input_path: Path) -> PlutoFlagState:
    state = PlutoFlagState(input_path=input_path)
    for flag, value in flags:
        reason = reject_known_flag(flag)
        if reason is not None:
            raise Reject(f"{flag}: {reason}")

        if flag == "--tile":
            state.tile = True
            state.tile_seen = True
        elif flag == "--notile":
            state.tile = False
            state.notile_seen = True
        elif flag == "--identity":
            state.identity = True
        elif flag == "--iss":
            state.iss = True
        elif flag == "--second-level-tile":
            state.second_level_tile = True
        elif flag == "--diamond-tile":
            state.diamond_tile = True
            state.diamond_seen = True
        elif flag == "--nodiamond-tile":
            state.diamond_tile = False
            state.nodiamond_seen = True
            state.full_diamond_tile = False
        elif flag == "--full-diamond-tile":
            state.diamond_tile = True
            state.diamond_seen = True
            state.full_diamond_tile = True
        elif flag in ("--parallel", "--parallelize"):
            state.parallel = True
            state.parallel_seen = True
        elif flag == "--noparallel":
            state.parallel = False
            state.no_parallel_seen = True
        elif flag == "--innerpar":
            state.innerpar_seen = True
            state.add_note("--innerpar is implicit in polopt's current --parallel route")
        elif flag == "--nointratileopt":
            state.no_intratileopt_seen = True
            state.add_note("--nointratileopt accepted because checked routes disable Pluto intra-tile rewriting")
        elif flag == "--noprevector":
            state.no_prevector_seen = True
            state.add_note("--noprevector accepted because polopt does not use Pluto codegen vector marking")
        elif flag == "--nounrolljam":
            state.no_unrolljam_seen = True
            state.add_note("--nounrolljam accepted because polopt does not use Pluto unroll-jam output")
        elif flag in ACCEPTED_NOOPS:
            state.add_note(f"{flag} accepted as a no-op for the checked polopt route")
        elif flag == "--unroll":
            raise Reject("--unroll: Pluto only accepts this as an abbreviation for --unrolljam; unroll-jam is not a checked polopt route")
        elif flag in VALUE_OPTIONS:
            if flag in ("--cloogf", "--cloogl", "--codegen-context", "-o"):
                raise Reject(f"{flag}: output/codegen shaping is outside the polopt checked route")
            raise Reject(f"{flag}: value {value!r} is not exposed through the checked polopt route")
        else:
            raise Reject(f"{flag}: not in the current Pluto-compatible checked subset")
    return state


def polopt_args_for_state(state: PlutoFlagState) -> list[str]:
    if state.tile_seen and state.notile_seen:
        raise Reject("--tile and --notile are both present; this wrapper rejects contradictory phase controls")
    if state.parallel_seen and state.no_parallel_seen:
        raise Reject("--parallel and --noparallel are both present; this wrapper rejects contradictory phase controls")
    if state.diamond_seen and state.nodiamond_seen:
        raise Reject("--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present; this wrapper rejects contradictory phase controls")
    if not state.no_intratileopt_seen:
        raise Reject("Pluto enables --intratileopt by default; pass --nointratileopt for the current checked polopt subset")
    if not state.no_prevector_seen:
        raise Reject("Pluto enables --prevector by default; pass --noprevector because polopt does not use Pluto codegen vector marking")
    if not state.no_unrolljam_seen:
        raise Reject("Pluto enables --unrolljam by default; pass --nounrolljam because polopt does not use Pluto unroll-jam output")
    if not state.parallel and not state.no_parallel_seen:
        raise Reject("Pluto enables --parallel by default; pass --noparallel or --parallel explicitly")
    if not state.diamond_tile and not state.nodiamond_seen:
        raise Reject("Pluto enables --diamond-tile by default; pass --nodiamond-tile or --diamond-tile explicitly")
    if state.identity and not state.notile_seen:
        raise Reject("--identity: current Pluto keeps tiling enabled by default; use --identity --notile for polopt's no-tiling identity route")
    if state.identity and state.tile_seen:
        raise Reject("--identity --tile: Pluto can tile identity schedules, but polopt has no checked identity+tiling route yet")
    if state.identity and state.parallel:
        raise Reject("--parallel requires a Pluto scheduling phase and cannot be combined with --identity")
    if state.second_level_tile and not state.tile:
        raise Reject("--second-level-tile requires tiling and cannot be combined with --notile")
    if state.second_level_tile and state.identity:
        raise Reject("--second-level-tile requires a tiled Pluto phase and cannot be combined with --identity")
    if state.second_level_tile and state.parallel:
        raise Reject("--second-level-tile is not yet supported with --parallel")

    if state.diamond_tile:
        if not state.tile:
            raise Reject("--diamond-tile requires tiling and cannot be combined with --notile")
        if state.identity:
            raise Reject("--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity")
        if state.iss:
            raise Reject("--diamond-tile is not yet supported with --iss")
        if state.parallel:
            raise Reject("--diamond-tile is not yet supported with --parallel")
        if state.second_level_tile:
            raise Reject("--diamond-tile is not yet supported with --second-level-tile")

    args: list[str] = []
    if state.identity:
        if state.iss:
            args.append("--iss")
        args.append("--identity")
    elif not state.tile:
        args.append("--notile")
    else:
        if state.iss:
            args.append("--iss")
        if state.second_level_tile:
            args.append("--second-level-tile")
        if state.full_diamond_tile:
            args.append("--full-diamond-tile")
        elif state.diamond_tile:
            args.append("--diamond-tile")
        if state.parallel:
            args.append("--parallel")
    return args


def main(argv: list[str]) -> int:
    try:
        cfg, rest = parse_wrapper_args(argv)
        flags, input_path = split_flags_and_input(rest)
        state = normalize_pluto_flags(flags, input_path)
        polopt_args = polopt_args_for_state(state)
    except (Reject, ValueError) as exc:
        print(f"[pluto-compat] reject: {exc}", file=sys.stderr)
        return 2

    cmd = [str(cfg.polopt), *polopt_args, str(state.input_path)]
    if cfg.explain or cfg.dry_run:
        print("[pluto-compat] accepted", flush=True)
        print(
            "[pluto-compat] polopt args:",
            " ".join(polopt_args) if polopt_args else "<default>",
            flush=True,
        )
        if state.notes:
            for note in state.notes:
                print(f"[pluto-compat] note: {note}", flush=True)
    if cfg.dry_run:
        return 0

    try:
        proc = subprocess.run(
            cmd,
            cwd=str(ROOT),
            text=True,
            timeout=cfg.timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        print("[pluto-compat] reject: polopt timed out", file=sys.stderr)
        return 124
    except OSError as exc:
        print(f"[pluto-compat] infrastructure error: failed to run polopt: {exc}", file=sys.stderr)
        return 127
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
