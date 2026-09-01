#!/usr/bin/env python3
"""Compile the existing typed-C test with output capture calls inserted."""

from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def insert_once(text: str, needle: str, replacement: str) -> str:
    require(text.count(needle) == 1, f"expected one insertion point: {needle[:80]}")
    return text.replace(needle, replacement, 1)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pretty", type=Path, required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    source = args.source.resolve()
    output = args.output.resolve()
    if output.exists() and args.force:
        shutil.rmtree(output)
    require(not output.exists(), f"output already exists: {output}")
    output.mkdir(parents=True)

    original = (source / "tests/typed-c-pipeline/test.ml").read_text(encoding="utf-8")
    captures = (
        (
            "  let output = run case (fun () -> CBand.coq_Opt_band source) in\n"
            "  let before = loop_stats source and after = loop_stats output in\n",
            "  let output = run case (fun () -> CBand.coq_Opt_band source) in\n"
            "  TypedProgramView.capture_loop case source output;\n"
            "  let before = loop_stats source and after = loop_stats output in\n",
        ),
        (
            "  let one = loop_stats ordinary and two = loop_stats output in\n",
            "  TypedProgramView.capture_loop case source output;\n"
            "  let one = loop_stats ordinary and two = loop_stats output in\n",
        ),
        (
            "      CBand.PrepareCore.prepared_codegen\n"
            "        (CBand.PolyLang.current_view_pprog split_pol))\n"
            "  in\n"
            "  let before = loop_stats source and after = loop_stats output in\n"
            "  if output = source || after.instrs <= before.instrs then\n",
            "      CBand.PrepareCore.prepared_codegen\n"
            "        (CBand.PolyLang.current_view_pprog split_pol))\n"
            "  in\n"
            "  TypedProgramView.capture_loop case source output;\n"
            "  let before = loop_stats source and after = loop_stats output in\n"
            "  if output = source || after.instrs <= before.instrs then\n",
        ),
        (
            "  let before = loop_stats source in\n"
            "  let rectangular = loop_stats no_diamond and diamond = loop_stats output in\n",
            "  TypedProgramView.capture_loop case source output;\n"
            "  let before = loop_stats source in\n"
            "  let rectangular = loop_stats no_diamond and diamond = loop_stats output in\n",
        ),
        (
            "  let stats, modes = parallel_stats output in\n"
            "  if modes.par <> 1 || modes.par_requested <> 1 || modes.vec <> 0 then\n",
            "  TypedProgramView.capture_parallel case source output;\n"
            "  let stats, modes = parallel_stats output in\n"
            "  if modes.par <> 1 || modes.par_requested <> 1 || modes.vec <> 0 then\n",
        ),
        (
            "  let stats, modes = parallel_stats output in\n"
            "  if modes.vec <> 1 || modes.vec_requested <> 1\n",
            "  TypedProgramView.capture_parallel case source output;\n"
            "  let stats, modes = parallel_stats output in\n"
            "  if modes.vec <> 1 || modes.vec_requested <> 1\n",
        ),
    )
    transformed = original
    for needle, replacement in captures:
        transformed = insert_once(transformed, needle, replacement)

    with tempfile.TemporaryDirectory(prefix="polcert-typed-programs-") as temporary:
        tmp = Path(temporary)
        pretty = tmp / "TypedProgramView.ml"
        test = tmp / "TypedProgramCapture.ml"
        makefile = tmp / "capture.mk"
        shutil.copy2(args.pretty, pretty)
        test.write_text(transformed, encoding="utf-8")
        makefile.write_text(
            f"COMPFLAGS += -I {tmp}\n"
            "TYPED_CAPTURE_OBJS := $(TYPED_C_PIPELINE_OBJS) "
            f"{pretty.with_suffix('.cmx')} {test.with_suffix('.cmx')}\n"
            ".PHONY: typed-program-capture\n"
            "typed-program-capture: $(TYPED_CAPTURE_OBJS)\n"
            "\t$(OCAMLOPT) -o /tmp/polcert-typed-program-capture "
            "$(LIBS) $(LINK_OPT) $+\n",
            encoding="utf-8",
        )
        command = [
            "make", "-f", "Makefile.extr", "-f", str(makefile),
            "typed-program-capture", "--no-print-directory",
        ]
        build = subprocess.run(
            command, cwd=source, text=True, capture_output=True, check=False
        )
        require(
            build.returncode == 0,
            f"typed program capture build failed:\n{build.stdout}\n{build.stderr}",
        )
        env = dict(__import__("os").environ)
        env["POLCERT_TYPED_PROGRAM_OUTPUT"] = str(output)
        run = subprocess.run(
            ["/tmp/polcert-typed-program-capture", "-conf", "polcert.ini"],
            cwd=source,
            env=env,
            text=True,
            capture_output=True,
            check=False,
        )
        require(
            run.returncode == 0,
            f"typed program capture failed:\n{run.stdout}\n{run.stderr}",
        )

    expected = {
        "ordinary-tiling-pointwise", "two-level-tiling-matmul",
        "iss-reverse-index", "diamond-stencil", "parallel-pointwise",
        "vector-pointwise",
    }
    actual = {path.name for path in output.iterdir() if path.is_dir()}
    require(actual == expected, f"typed capture cases: expected {expected}, got {actual}")
    print(f"wrote {len(actual)} typed program comparisons to {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
