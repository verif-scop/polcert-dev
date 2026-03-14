Require Import PolIRs.
Require Import TInstr.
Require Import PolyLang. 
Require Import PolyLoop.
Require Import Loop.
Require Import Result.
Require Import OpenScop.
Require Import String.
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

   Definition to_phase_openscop (cpol: PolyLang.t) : option OpenScop :=
      PolyLang.to_openscop cpol.
End TPolIRs.
