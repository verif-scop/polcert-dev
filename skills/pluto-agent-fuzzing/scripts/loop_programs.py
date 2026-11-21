#!/usr/bin/env python3
"""Turn PolCert loop programs into complete C programs for differential runs.

usage: loop_programs.py source PROG.loop OUT.c
       loop_programs.py optimized PROG.loop OPTIMIZED.loop OUT.c

Run from a PolCert tree; this reuses tools/end_to_end_c/generated_harness.py,
which declares every array, initializes it deterministically, runs the kernel
and prints a checksum.  The source program marks its kernel with #pragma scop
and declares the loop iterators outside the loops, as Pluto's C frontend
expects.  The optimized program runs PolCert's output loop instead.
"""
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path.cwd() / "tools" / "end_to_end_c"))
from generated_harness import build_harness, render_program_source  # noqa: E402

DECL = re.compile(r"for \(long long (\w+) =")


def source_program(loop_text):
    info = build_harness("prog", loop_text, loop_text)
    text = render_program_source(info, optimized=False)
    kernel = info.baseline_kernel.rstrip()
    iters = sorted(set(DECL.findall(kernel)))
    decl = f"  long long {', '.join(iters)};\n" if iters else ""
    scop = decl + "#pragma scop\n" + DECL.sub(r"for (\1 =", kernel) + "\n#pragma endscop"
    assert kernel in text
    return text.replace(kernel, scop, 1)


def optimized_program(loop_text, optimized_text):
    info = build_harness("prog", loop_text, optimized_text)
    return render_program_source(info, optimized=True)


def main():
    mode, args = sys.argv[1], sys.argv[2:]
    read = lambda p: pathlib.Path(p).read_text()
    if mode == "source":
        out, text = args[1], source_program(read(args[0]))
    elif mode == "optimized":
        out, text = args[2], optimized_program(read(args[0]), read(args[1]))
    else:
        sys.exit(__doc__)
    pathlib.Path(out).write_text(text)


if __name__ == "__main__":
    main()
