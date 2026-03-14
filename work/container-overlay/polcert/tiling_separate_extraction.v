Require Import OpenScop.
Require Import Result.
Require Import Linalg.
Require Import ZArith.
Require Import List.
Require Import String.
Require Import BinNat.
Require Import OpenScopAST.
Require Import Floats.

Require Import PolyLang.
Require Import InstrTy.
Require Import ImpureAlarmConfig.
Require Import TilingWitness.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import SPolIRs.
Require Import STilingOpt.

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Set Extraction AccessOpaque.

Extraction Blacklist String List Int.
Extraction Blacklist Misc.

Extract Inlined Constant CoqAddOn.posPr => "CoqPr.posPr'".
Extract Inlined Constant CoqAddOn.posPrRaw => "CoqPr.posPrRaw'".
Extract Inlined Constant CoqAddOn.zPr => "CoqPr.zPr'".
Extract Inlined Constant CoqAddOn.zPrRaw => "CoqPr.zPrRaw'".

Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Load extractionMachdep.

Extract Constant Z.pred =>
  "fun x -> add x (Zneg Coq_xH)".
Extract Constant Z.iter =>
  "fun n f x -> match n with | Zpos p -> Pos.iter f x p | _ -> x".
Extract Constant Z.odd =>
  "function | Z0 -> false | Zpos (Coq_xO _) -> false | Zneg (Coq_xO _) -> false | _ -> true".
Extract Constant Z.div2 =>
  "function | Z0 -> Z0 | Zpos Coq_xH -> Z0 | Zpos p -> Zpos (Pos.div2 p) | Zneg p -> Zneg (Pos.div2_up p)".
Extract Constant Z.log2 =>
  "function | Zpos (Coq_xI p) -> Zpos (Pos.size p) | Zpos (Coq_xO p) -> Zpos (Pos.size p) | _ -> Z0".
Extract Constant Z.log2_up =>
  "fun a -> match compare (Zpos Coq_xH) a with | Lt -> succ (log2 (pred a)) | _ -> Z0".

Extract Constant SPolIRs.scop_scheduler => "Scheduler.scop_scheduler".
Extract Constant AST.ident_to_varname => "Camlcoq.extern_atom'".
Extract Constant AST.iterator_to_varname => "Camlcoq.iterator_to_varname".
Extract Constant AST.varname_to_ident => "Camlcoq.varname_to_ident".
Extract Constant AST.bind_ident_varname => "Camlcoq.bind_ident_varname".
Extract Constant PolyBase.free_ident => "Camlcoq.free_ident".

Extraction Inline CoreAlarmed.Base.pure CoreAlarmed.Base.imp.

Cd "extraction".

Set Warnings "-extraction-ambiguous-name".
Set Warnings "-extraction-opaque-accessed".

Separate Extraction STilingOpt.
