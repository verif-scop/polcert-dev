Require Import OpenScop.

Require Import Result.
Require Import Linalg.
Require Import ZArith.
Require Import List.
Require Import String.
Require Import BinNat.
Require Import OpenScopAST.
Require Import Floats.

Require Import CodeGen.
Require Import PolyLang.
Require Import InstrTy.
Require Import ImpureAlarmConfig.
Require Import Linalg.
Require Import ZArith.
Require Import TopoSort.

Require Import Memdata.
(* Require Import Machregs. *)

Require Import PolOpt.
Require Import ParallelLoop.
Require Import ParallelCodegen.

Require Import CSample1.
Require Import CSample2.
Require Import CSample3.
Open Scope Z_scope.
Import ListNotations.

Require Extraction.

Set Extraction AccessOpaque.

Extract Inlined Constant CoqAddOn.posPr => "CoqPr.posPr'".
Extract Inlined Constant CoqAddOn.posPrRaw => "CoqPr.posPrRaw'".
Extract Inlined Constant CoqAddOn.zPr => "CoqPr.zPr'".
Extract Inlined Constant CoqAddOn.zPrRaw => "CoqPr.zPrRaw'".

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inlined Constant topo_sort_untrusted => "(fun l -> (Topo.coq_toposort l, true))".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist String List Int.
Extraction Blacklist Misc. (* used by the VPL *)

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Load extractionMachdep.

(* Keep BinInt.Z extraction compatible with other extracted stdlib modules
   such as Zbits/Initializers/IEEE754_extra that rely on these APIs. *)
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

Extract Inlined Constant Debugging.failwith =>
  "(fun st mesg _ -> raise (CertcheckerConfig.CertCheckerFailure (st, (CoqPr.charListTr mesg))))".

Extraction Inline CoreAlarmed.Base.pure CoreAlarmed.Base.imp.


Extract Constant location =>
"{ lineno : int;
   filename: string;
   byteno: int;
 }".

Definition sample_rel_meta := {|
    OpenScop.row_nb:= 0; 
    OpenScop.col_nb:= 0; 
    OpenScop.out_dim_nb:= 0; 
    OpenScop.in_dim_nb:= 0;
    OpenScop.local_dim_nb:= 0;
    OpenScop.param_nb:= 0;
|}.

Definition sample_ctxt_rel := {|
    OpenScop.rel_type := OpenScop.CtxtTy;
    OpenScop.meta := sample_rel_meta;
    OpenScop.constrs:= nil;
|}.

Definition sample_domain_rel := {|
    OpenScop.rel_type := OpenScop.DomTy;
    OpenScop.meta := sample_rel_meta;
    OpenScop.constrs:= (true, (2%Z :: 0%Z :: nil))::((true, (1%Z :: 3%Z :: nil))::nil);
|}.

Definition sample_scattering_rel := {|
    OpenScop.rel_type := OpenScop.ScttTy;
    OpenScop.meta := sample_rel_meta;
    OpenScop.constrs:= (true, (2%Z :: 0%Z :: nil))::((true, (1%Z :: 3%Z :: nil))::nil);
|}.


Definition sample_read_rel := {|
    OpenScop.rel_type := OpenScop.ReadTy;
    OpenScop.meta := sample_rel_meta;
    OpenScop.constrs:= (true, (2%Z :: 0%Z :: nil))::((true, (1%Z :: 3%Z :: nil))::nil);
|}.

Definition sample_write_rel := {|
    OpenScop.rel_type := OpenScop.WriteTy;
    OpenScop.meta := sample_rel_meta;
    OpenScop.constrs:= (true, (2%Z :: 0%Z :: nil))::((true, (1%Z :: 3%Z :: nil))::nil);
|}.


Definition sample_maywrite_rel := {|
    OpenScop.rel_type := OpenScop.MayWriteTy;
    OpenScop.meta := sample_rel_meta;
    OpenScop.constrs:= (true, (2%Z :: 0%Z :: nil))::((true, (1%Z :: 3%Z :: nil))::nil);
|}.

Open Scope string_scope.

Definition sample_ctxt:OpenScop.ContextScop := {| 
    OpenScop.lang := "C"; 
    OpenScop.param_domain := sample_ctxt_rel;
    OpenScop.params := Some ("N"::("T"::nil)); 
|}.

Definition id1 := "i".
Definition id2 := "j".

Definition sample_stmt_body_ext := OpenScop.StmtBody (id1::(id2::nil)) (ArrAssign (ArrAccess "arr"%string nil) (ArrAtom (AInt 0%Z)))%nat.

Definition sample_stmt_exts := sample_stmt_body_ext::nil.

(* Definition sample *)
Definition sample_stmt := {|
    OpenScop.domain:= sample_domain_rel; 
    OpenScop.scattering:= sample_scattering_rel; 
    OpenScop.access:= sample_write_rel :: nil; 
    OpenScop.stmt_exts_opt:= Some sample_stmt_exts;
|}.

Definition sample_glb_array_ext := OpenScop.ArrayExt ((1%positive, "A")::nil).
Definition sample_glb_comment_ext := OpenScop.CommentExt "welcome to coq-openscop".
Definition sample_glb_scat_ext := OpenScop.ScatNamesExt ("t1"::"t2"::nil).
Definition sample_glb_coord_ext := OpenScop.CoordExt None (34%nat, 0%nat) (38%nat, 0%nat) 4%nat.
Definition sample_glb_ext := sample_glb_array_ext::sample_glb_comment_ext::sample_glb_scat_ext::sample_glb_coord_ext::nil.
Definition sample_scop := {| 
    OpenScop.context := sample_ctxt; 
    OpenScop.statements := sample_stmt::(sample_stmt::nil); 
    OpenScop.glb_exts := sample_glb_ext;
|}.

(** sample CPol.t *)
Require Import PolyBase.
Require Import CPolIRs.
Require Import TPolIRs.
Require Import SPolIRs.
Extraction Inline CoreAlarmed.Base.pure CoreAlarmed.Base.imp.

Extract Constant PolOpt.time  => "Timing.time_coq".
Extract Constant print_CompCertC_stmt => "PrintCsyntax.print_if".
Extract Constant CPolIRs.scop_scheduler => "Scheduler.scop_scheduler".
Extract Constant CPolIRs.phase_scop_scheduler => "Scheduler.phase_scop_scheduler".
Extract Constant CPolIRs.phase_scop_scheduler_with_iss => "Scheduler.run_pluto_phase_pipeline_with_iss".
Extract Constant CPolIRs.infer_iss_from_source_scop => "PhaseISS.cpol_infer_iss_from_source_scop".
Extract Constant CPolIRs.infer_tiling_witness_scops => "Scheduler.infer_tiling_witness_scops".
Extract Constant TPolIRs.scop_scheduler => "Scheduler.scop_scheduler".
Extract Constant TPolIRs.phase_scop_scheduler => "Scheduler.phase_scop_scheduler".
Extract Constant TPolIRs.phase_scop_scheduler_with_iss => "Scheduler.run_pluto_phase_pipeline_with_iss".
Extract Constant TPolIRs.infer_iss_from_source_scop => "PhaseISS.tpol_infer_iss_from_source_scop".
Extract Constant TPolIRs.infer_tiling_witness_scops => "Scheduler.infer_tiling_witness_scops".
Extract Constant SPolIRs.scop_scheduler => "Scheduler.scop_scheduler".
Extract Constant SPolIRs.phase_scop_scheduler => "Scheduler.phase_scop_scheduler".
Extract Constant SPolIRs.phase_scop_scheduler_with_iss => "Scheduler.run_pluto_phase_pipeline_with_iss".
Extract Constant SPolIRs.infer_iss_from_source_scop => "PhaseISS.spol_infer_iss_from_source_scop".
Extract Constant SPolIRs.infer_tiling_witness_scops => "Scheduler.infer_tiling_witness_scops".
Extract Constant PolOpt.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
Extract Constant AST.ident_to_varname => "Camlcoq.extern_atom'".
Extract Constant AST.iterator_to_varname => "Camlcoq.iterator_to_varname".
Extract Constant AST.varname_to_ident => "Camlcoq.varname_to_ident".
Extract Constant AST.bind_ident_varname => "Camlcoq.bind_ident_varname".


Extract Constant PolyBase.free_ident => "Camlcoq.free_ident".

Cd "extraction".

Require Import Initializers.
Require Import Ctyping.
Require Import CPolOpt.
Require Import TPolOpt.
Require Import SPolOpt.
Require Import STilingOpt.
Require Import TPolValidator.


Set Warnings "-extraction-ambiguous-name". (* This warning does not matter *)
Set Warnings "-extraction-opaque-accessed". (* To be fixed in VPL *)

Separate Extraction Archi Result AST Csyntax BinNums BinPos BinNat Floats Coq.ZArith.BinInt.Z ZArith_dec Ring_polynom_AddOnQ CstrLCF ProgVar LinTerm sample_scop OpenScop OpenScopAST PolyLang CPolIRs CSample1.sample_cpol CSample2.sample_cpol CSample3.sample_cpol Integers Memdata Ctypes Ctyping Initializers Debugging Qcanon NumC CoqAddOn ParallelLoop ParallelCodegen CPolOpt TPolIRs TPolOpt SPolIRs SPolOpt STilingOpt TPolValidator.
