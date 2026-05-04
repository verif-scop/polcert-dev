# Artifact Submission Goal

Date: 2026-05-04

## Goal

The artifact should make the paper's capability claims executable. A reviewer
should be able to run one documented command and see:

- which verified routes build and run;
- which Pluto-style requests map to checked `polopt` routes;
- which requests are rejected, with concrete reasons;
- which theorem and proof-surface checks support the claimed routes.

This is not a performance goal. Pluto remains the optimizer oracle. The artifact
goal is to show that PolCert/PolOpt accepts a broad, well-explained, checked
subset of Pluto's optimization surface.

## Current Baseline

Already available:

- strict generated loop suite: `62 / 62`;
- native `polopt --pluto-compat` suite: `21 / 21`;
- diamond suite over Pluto stencil fixtures:
  - six true diamond-effect cases;
  - two accepted no-effect cases;
  - eleven Pluto/Clan frontend-rejected C inputs;
- Pluto fork test suite: `65 / 65`;
- pushed Pluto support commits for phase-aligned dumps, ISS bridge export,
  staged readscop regression, and submodule-status cleanup.

The missing artifact work is packaging and route closure, not another
standalone proof inventory.

## Executable Plan

### 1. Native Pluto-Compatible `polopt` CLI

Problem:
The Pluto-style flag filter must live in the same driver that runs verified
extraction and code generation, not in an extra user-facing wrapper.

Target:
Keep the Pluto-style flag filter in `polopt` itself.

Acceptance criteria:

- `polopt` accepts Pluto-style optimizer flags directly.
- Supported combinations normalize to checked internal routes.
- Unsupported combinations fail before optimization and print a reason.
- The existing compatibility suite exercises the native CLI, not only the
  wrapper.

Implementation steps:

1. Keep `syntax/SLoopCli.ml` as the native compatibility filter.
2. Keep Python only as suite/report infrastructure, not as a public compiler
   entry point.
3. Maintain native-CLI tests for default tiling, affine-only, second-level,
   parallel, diamond, full diamond, and all important rejection paths.

### 2. One-Command Artifact Check

Problem:
The artifact has many useful suites, but no single reviewer entry point.

Target:
Provide:

```sh
make artifact-check
```

Acceptance criteria:

- The command writes a machine-readable summary.
- The command runs the lightweight submission-facing checks by default.
- A fuller mode can also run proof build and strict generated suites.

Implementation steps:

1. Add `tools/artifact/run_artifact_check.py`.
2. Add `make artifact-check` and `make artifact-check-full`.
3. Emit `artifact-results.json` under a caller-chosen output directory.
4. Keep the default check short enough for reviewer iteration; put heavier
   proof/suite commands behind `artifact-check-full`.

### 3. Diamond Route Closure

Problem:
The current diamond route is strong but narrow. It supports the sequential,
non-ISS, single-level tiled route:

```text
before -> mid_diamond -> posttile -> after
 affine      tiling        affine
```

The remaining work is not "support diamond at all"; it is to support diamond to
the limit of the surrounding framework.

Target:
Make diamond a first-class artifact route with precise support and rejection
behavior.

Acceptance criteria:

- The four-phase diamond route has a top-level driver/theorem story matching
  the executable path.
- The diamond suite reports frontend rejections separately from validator
  rejections.
- Heavy diamond cases have stable timeout settings.
- Combinations with ISS, parallel, and second-level tiling are either supported
  or rejected with tested reasons.

Implementation steps:

1. Stabilize the current suite:
   - record rejection reasons in `summary.json`;
   - distinguish `pluto_frontend_rejected`, `validator_rejected`, and
     `timeout`;
   - raise the default timeout for known heavy cases.
2. Close the four-phase theorem/driver gap:
   - name the accepted phase object in the driver;
   - expose the route as one checked pipeline result;
   - add a theorem-facing wrapper that composes affine, tiling, and affine
     validation for the four-phase path.
3. Push combination support as far as the current proof architecture permits:
   - `diamond + second-level`: validate two tiling boundaries or introduce a
     multi-level witness;
   - `diamond + parallel-current`: validate diamond first, then certify the
     selected parallel dimension on the resulting current view;
   - `diamond + parallel`: same as above, using Pluto's hint;
   - `diamond + ISS`: compose ISS split validation before diamond witness
     recovery, including the split-statement mapping.
4. Keep correct rejections:
   - `diamond + notile`;
   - `diamond + identity`, unless a meaningful identity-diamond route is
     designed and tested.

### 4. Second-Level Tiling Suite and Boundaries

Problem:
Second-level tiling is the next useful route after ordinary tiling and diamond,
but its combination boundary is still thin.

Target:
Make second-level tiling an explicit artifact capability.

Acceptance criteria:

- The second-level suite records supported and rejected combinations.
- `--iss --second-level-tile` has a focused case.
- `--second-level-tile --parallel` and
  `--second-level-tile --parallel-current d` are supported or rejected with
  tested reasons.

Implementation steps:

1. Extend `tools/second_level_tiling/suite_manifest.json`.
2. Add a dedicated ISS + second-level fixture if route normalization already
   supports it.
3. Add explicit rejection tests for every unsupported composition.
4. If supporting parallel composition, validate the second-level tiled program
   before invoking the parallel checker.

### 5. Automatic Capability Matrix and Proof Report

Problem:
The paper and docs should not hand-maintain route counts and support tables.

Target:
Generate:

```sh
make artifact-capability-matrix
make proof-report
```

Acceptance criteria:

- The capability matrix includes every Pluto-style flag class that matters for
  the paper.
- Every unsupported item has a reason and a plausible implementation path.
- The proof report records admits, aborts, theorem-surface names, and
  theorem-to-CLI mapping notes.

Implementation steps:

1. Add `tools/artifact/generate_capability_matrix.py`.
2. Add `tools/artifact/proof_report.py`.
3. Make both tools write JSON for paper/table generation.
4. Wire both tools into `make artifact-check`.

## Immediate Implementation Slice

This slice starts now:

- add `make artifact-check`;
- add `make artifact-capability-matrix`;
- add `make proof-report`;
- update the diamond suite to report concrete unsupported reasons;
- keep diamond theorem closure and route-combination support as the next
  implementation slice.
