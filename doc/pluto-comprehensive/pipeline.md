# Pluto Pipeline

This document records the actual execution order of Pluto as used by the
artifact. The focus is not "which optimizations Pluto can theoretically do", but
"which phases run in practice, in what order, and which IR objects each phase
changes".

For the naming and layering of the verified internal PolCert pipeline, see:

- [verified-phase-pipeline.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-phase-pipeline.md)

For the design rationale of the internal verified pipeline, see:

- [verified-pipeline-design.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-pipeline-design.md)

## 1. CLI Top-Level Flow

The CLI entry point is concentrated in:

- `/pluto/tool/main.cpp:184-904`

At a high level the flow is:

```text
parse options
normalize options

if PET:
  extract PET scop
  convert PET -> PlutoProg
else:
  read source or .scop
  maybe dump before.scop
  convert OSL/OpenScop -> PlutoProg

if ISS:
  apply ISS

if not identity:
  pluto_auto_transform()

recompute dependence directions/satisfaction

if tile:
  pluto_tile()
else if intratileopt:
  pluto_intra_tile_optimize()

if parallel && !tile && !identity:
  pluto_create_tile_schedule()

if dumpscop:
  pluto_populate_scop()
  write after.scop

emit .regtile
emit .cloog
emit code with CLooG + AST annotations
```

## 2. Option Parsing And Normalization

### 2.1 Parsing

The CLI option table lives in:

- `/pluto/tool/main.cpp:198-277`

From this table alone you can already see:

- which options are always compiled into the current binary
- which options only exist when GLPK/Gurobi support is enabled
- which options may parse successfully but later be disabled or ignored

### 2.2 Normalization

Option normalization happens in:

- `/pluto/tool/main.cpp:386-543`

Important normalization rules:

1. `isldep` and `candldep` cannot both be enabled.
2. If neither is requested, Pluto defaults to `isldep`.
3. `lastwriter` only works with `isldep`.
4. `second-level-tile` and `determine-tile-size` cannot both be enabled.
5. `tile = 0` forces `diamondtile` and `fulldiamondtile` off.
6. `multipar = 1 && parallel = 0` implicitly enables `parallel`.
7. typed/hybrid/delayed-cut configurations are pushed toward the DFP path, but
   fail early if the binary does not have the required solver support.

This matters because Pluto's real phase choice is not driven directly by raw CLI
flags. It is driven by a normalized configuration.

## 3. Front-End Split

The front-end split is in:

- `/pluto/tool/main.cpp:552-672`

### 3.1 PET Path

When `options->pet` is true, Pluto uses:

- `/pluto/tool/main.cpp:553-579`
- `/pluto/tool/pet_to_pluto.cpp`

The effective flow is:

1. `pet_scop_extract_from_C_source()`
2. `pet_to_pluto_prog()`
3. rebuild `PlutoProg` using PET-side schedule/access information

The PET path can perform dependence analysis, scheduling, tiling, and codegen.
However, in the current fork, `--dumpscop` is not supported for PET. The source
code prints:

```text
[Pluto] --dumpscop not support pet frontend yet
```

at:

- `/pluto/tool/main.cpp:647-649`

### 3.2 Clan / `readscop` Path

The non-PET path lives in:

- `/pluto/tool/main.cpp:579-672`

It splits into:

- `--readscop`: `osl_scop_pread()` reads OpenScop directly
- default C path: `clan_scop_extract()` extracts OpenScop from C

On this path, `--dumpscop` runs before any scheduling and writes the extracted
input SCoP as `.beforescheduling.scop`:

- `/pluto/tool/main.cpp:621-649`

This is why PolCert/PolOpt can obtain a concrete `before.scop` model from Pluto.

## 4. OpenScop/PET To `PlutoProg`

### 4.1 OSL/OpenScop Conversion

The OSL conversion entry point is:

- `/pluto/tool/osl_pluto.c:1605`

`osl_scop_to_pluto_prog()` does the following:

1. create a `PlutoProg`
2. import parameters and parameter context
3. import array names
4. traverse statements and construct internal `Stmt` objects
5. compute dependences
6. initialize hyperplane metadata

For verification, the key point is that Pluto imports the *entire* polyhedral
model, not only a schedule:

- domains
- schedules / scattering
- accesses
- parameters
- dependences

### 4.2 `pluto_populate_scop()` Write-Back

The function that writes the optimized program back to OpenScop is:

- `/pluto/tool/osl_pluto.c:586-715`

It performs all of the following:

1. replace each statement domain with Pluto's internal domain
2. replace the original scattering with Pluto's current `trans`
3. update iterator lists in the statement body if iterator counts changed
4. insert blank input dimensions into accesses when iterator counts grow
5. rebuild scatnames
6. write loop metadata such as parallel/vector annotations
7. write the `pluto_unroll` extension

Therefore `after.scop` is not "the original SCoP plus one new scattering". It
is a rewritten OpenScop object.

## 5. Dependence Analysis

### 5.1 OSL Path: ISL / Candl

Dependence analysis on the OSL path happens in:

- `/pluto/tool/osl_pluto.c:1665-1693`

The default path is ISL:

- `/pluto/tool/osl_pluto.c:1186-1457`
- `/pluto/lib/program.cpp:622-695`

Pluto computes dependences from:

- statement domains
- statement accesses
- the current schedule/scattering

It then calls `isl_union_map_compute_flow()` to derive:

- RAW
- WAR
- WAW
- RAR, when `--rar` is enabled

`lastwriter` changes the flow computation method, so it changes more than just
the count of dependences; it changes the representation itself.

The Candl path lives in:

- `/pluto/tool/osl_pluto.c:1459-1599`

### 5.2 PET Path

Dependence analysis on the PET path is in:

- `/pluto/tool/pet_to_pluto.cpp:76-169`

Compared to the OSL path, PET first encodes read/write accesses into tuple
names, constructs access-aware schedules, and then still lowers to
`compute_deps_isl()`.

### 5.3 Consequence For Verification

Pluto's notion of a "legal schedule" does not depend only on source-level
semantics. It depends on:

- the currently extracted polyhedral model
- the current dependence representation
- the current schedule encoding

That is why the most stable validation target is the actual polyhedral model
Pluto consumed and then produced, not a guessed schedule property reconstructed
from source syntax alone.

## 6. ISS Runs Before The Scheduler

The ISS entry point is:

- `/pluto/tool/main.cpp` before `pluto_auto_transform()`

The important semantic point is:

- classic scheduling mostly reorders existing statements and schedules
- ISS may first rewrite the statement/domain structure and only then pass the
  result to the scheduler

So ISS is not "just another scheduler sub-step". It is a program rewrite that
precedes scheduling.

## 7. `pluto_auto_transform()`: Classic Pluto Core

### 7.1 Initialization

The classic route initializes scheduling structures, dependence constraints, and
hyperplane bookkeeping before entering its search loop.

### 7.2 Precut / Initial Cut

Pluto may insert explicit cuts early to control fusion/distribution structure
before it starts searching for better hyperplanes.

### 7.3 Classic Hyperplane Search Loop

The classic loop repeatedly:

1. builds the current scheduling problem
2. finds a valid new hyperplane if possible
3. updates dependence satisfaction
4. inserts cuts when heuristics decide fusion should stop
5. switches between eager/lazy strategies as needed

### 7.4 Where Hyperplanes Are Actually Solved

`find_permutable_hyperplanes()` is the central solver-facing function.

The classic route effectively:

1. collects legality constraints
2. adds coefficient bounds
3. adds non-triviality constraints
4. adds linear independence constraints
5. solves a lexicographic minimum problem

So classic Pluto is fundamentally an optimization problem over legality
constraints, not a sequence of ad hoc rewrites.

### 7.5 Cut Heuristics

Cut heuristics explicitly add schedule structure such as distribution boundaries.
These cuts are one way Pluto prevents some candidate fusions from being pursued
further.

### 7.6 Diamond-Tiling Hook In The Classic Route

Diamond tiling is not a completely separate post-pass. In the classic route it
hooks into the discovery of the first suitable permutable band.

From the proof-boundary viewpoint, this is the key fact: diamond changes the
affine band that later gets tiled, rather than introducing a separate tiling
semantics after the ordinary tiling machinery has already run.

## 8. DFP Route

DFP-related code is present in the source tree and can be located from the
`pluto_auto_transform()` DFP branch. The high-level flow is:

1. build a fusion-conflict graph
2. color the graph
3. select/distribute groups
4. derive schedules
5. optionally apply diamond tiling
6. re-check dependence satisfaction, falling back to a more conservative
   strategy if needed

### Current Artifact Status

DFP is a real source-level capability, but not a uniformly available artifact
capability in the current binary:

- some related CLI options are conditionally compiled
- `--typedfuse` can parse but later fails if GLPK/Gurobi support is unavailable

Therefore, in this artifact:

- DFP is a source-level capability worth documenting
- it is not a uniformly available runtime capability

## 9. `pluto_tile()`: Fixed Post-Scheduling Tile Pipeline

The tiling entry point is the `pluto_tile()` route. Its execution order is not
arbitrary; it is a fixed mini-pipeline:

1. find outermost/innermost permutable bands
2. optionally add a tile band for innermost parallel loops
3. build tiled schedules
4. recompute dependence directions/satisfaction
5. if diamond tiling is enabled, apply diamond-tile rescheduling
6. if intra-tile optimization is enabled, run intra-tile optimization
7. if parallel tiling is enabled, create the tile-space parallel schedule

So "tiling" is not a single step. It is its own sequence of transformations.

When diamond is enabled, the most accurate summary is therefore:

- first, diamond-aware affine-band selection/rescheduling
- then, ordinary tiling machinery over that modified band

## 10. Schedule Dimensions May Grow Even Without Tiling

This is an easy point to miss.

When Pluto runs with:

- `parallel = 1`
- `tile = 0`
- and a suitable non-identity schedule

it may still call:

- `/pluto/lib/tile.c:473-483` `pluto_create_tile_schedule()`

This can add wavefront/pipelined schedule structure even without domain growth.
Therefore:

- `--parallel --notile` is not "just add an OpenMP pragma"
- it is still a real polyhedral transformation

## 11. Post-Transform Locality / Vector / Unroll Logic

### 11.1 Locality / Vector Choice

After the main schedule is chosen, Pluto scores loops for spatial reuse,
temporal reuse, and vectorizability, then tries to move a profitable loop into
the innermost position.

### 11.2 Unroll-Jam Candidates

Unroll-jam candidate selection and profitability are heuristic. This is not part
of the core legality proof boundary; it belongs to the post-transform/codegen
side.

## 12. Codegen: `.cloog` -> CLAST -> C

The code generation path includes:

- emitting `.cloog`
- building CLAST
- using CLAST annotations for properties such as parallel/vector metadata

Semantically, this boundary should be read carefully:

- parallel/vector/unroll annotations do affect the generated C
- but they are no longer purely polyhedral objects
- for verification, this belongs more naturally to the codegen-correctness side
  than to the schedule/domain-correctness side

## 13. A Special Point About The `libpluto` Path

`libpluto`'s `pluto_schedule_prog()` largely mirrors the CLI phase order, but it
also contains an especially relevant normalization step:

- it can move some tiling-induced domain growth information into schedule
  constraints and then drop the additional statement dimensions

This suggests an important verification direction:

- one does not necessarily have to validate every tiling result directly in the
  most expanded OpenScop domain representation
- some cases may first be normalized back into "original point-domain + richer
  schedule relation"

That observation remains relevant even now that the checked phase-aligned tiling
route is working, because it highlights a natural normalization boundary between
external Pluto output and internal verified consumption.
