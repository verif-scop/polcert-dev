Require Import List.
Require Import ZArith.

Require Import InstrTy.
Require Import PolyBase.

(* Transitional note:
   the earlier split-interface sketch is no longer the preferred direction.
   The refined witness-centered design keeps [INSTR] unchanged and makes the
   current-to-source projection explicit inside PolyLang.  This file is kept as
   a design artifact to record the rejected alternative, not as the target
   implementation. *)

Module Type WITNESSED_INSTR_ALT.
  Include INSTR.

  Parameter access_args_related : list Z -> list Z -> Prop.

  Parameter valid_access_function_related :
    list AccessFunction -> list AccessFunction -> t -> Prop.

  Axiom valid_access_function_related_spec :
    forall wl rl i,
      valid_access_function_related wl rl i <->
      forall src_args acc_args st st' wcells rcells,
        instr_semantics i src_args wcells rcells st st' ->
        access_args_related src_args acc_args ->
        valid_access_cells acc_args wcells wl /\
        valid_access_cells acc_args rcells rl.

  Parameter access_function_checker_related :
    list AccessFunction -> list AccessFunction -> t -> bool.

  Axiom access_function_checker_related_correct :
    forall wl rl i,
      access_function_checker_related wl rl i = true ->
      valid_access_function_related wl rl i.
End WITNESSED_INSTR_ALT.
