# <Option or stage>: <what goes wrong, in one line>

**Tracker:** `<repository>`
**Affected:** <versions and commits checked, each marked wrong / correct / aborts>

<Two or three sentences: the program, the flags, and the observable
symptom. Say whether the output is wrong without OpenMP.>

## Reproducer

`repro.c`:

```c
<minimal self-contained C program with #pragma scop, deterministic
initialization and a printed checksum>
```

```sh
printf '%s\n' <sizes> > tile.sizes   # only if tiling is involved
polycc repro.c <flags> -o out.c
gcc -O0 repro.c -o orig -lm && ./orig
gcc -O0 out.c -o pluto -lm && ./pluto
# parallel output: gcc -O0 -fopenmp out.c -o pluto -lm, run several thread counts
```

**Expected:** `<output of the original program>`
**Actual:** `<output of Pluto's code, and under which configurations>`

Generated code (excerpt, if it helps):

```c
<the few lines that show the defect>
```

## Cause

<File and line in the source, and the invariant that breaks.>

## Fix

<The fix if known (a patch or a description), otherwise "No fix yet".>
