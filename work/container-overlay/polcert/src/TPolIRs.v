Require Import PolIRs.
Require Import TInstr.
Require Import PolyLang. 
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import String.
Require Import ISSWitness.
Require Import TilingWitness.

Local Open Scope string_scope.

Module TPolIRs <: POLIRS with Module Instr := TInstr.
   Module Instr := TInstr.
   Module State := State.
   Module Ty := Ty.
   Module PolyLang := PolyLang TInstr.
   Module PolyLoop := PolyLoop TInstr.
   Module Loop := Loop TInstr.
   Parameter scop_scheduler: OpenScop -> result OpenScop.
   Parameter phase_scop_scheduler: OpenScop -> result (OpenScop * OpenScop).
   Parameter phase_scop_scheduler_with_iss :
     OpenScop -> result (OpenScop * OpenScop).
   Parameter infer_iss_from_source_scop :
     PolyLang.t -> OpenScop -> result (option (PolyLang.t * iss_witness)).
   Parameter infer_tiling_witness_scops:
     OpenScop -> OpenScop -> result (list statement_tiling_witness).

   Definition scheduler cpol :=
      match PolyLang.to_openscop cpol with
      | Some inscop =>
         match scop_scheduler inscop with
         | Okk outscop => PolyLang.from_openscop cpol outscop
         | Err msg => Err msg
         end
      | None => Err "Transform pol to openscop failed"
      end
   .
   Definition affine_scheduler := scheduler.

   Definition export_for_phase_scheduler (cpol: PolyLang.t) : option OpenScop :=
      PolyLang.to_openscop cpol.
   Definition export_for_pluto_phase_pipeline := export_for_phase_scheduler.
   Definition to_phase_openscop := export_for_phase_scheduler.
   Definition run_pluto_phase_pipeline := phase_scop_scheduler.
   Definition run_pluto_phase_pipeline_with_iss :=
     phase_scop_scheduler_with_iss.
End TPolIRs.
