open BinInt
open BinNums
open BinPos
open Binary
open BinarySingleNaN
open Datatypes
open SpecFloat
open ZArith_dec
open Zaux

(** val coq_Beq_dec :
    coq_Z -> coq_Z -> Binary.binary_float -> Binary.binary_float -> bool **)

let coq_Beq_dec _ _ f1 f2 =
  match f1 with
  | Binary.B754_zero s1 ->
    (match f2 with
     | Binary.B754_zero s2 ->
       if s1 then if s2 then true else false else if s2 then false else true
     | _ -> false)
  | Binary.B754_infinity s1 ->
    (match f2 with
     | Binary.B754_infinity s2 ->
       if s1 then if s2 then true else false else if s2 then false else true
     | _ -> false)
  | Binary.B754_nan (s1, p1) ->
    (match f2 with
     | Binary.B754_nan (s2, p2) ->
       if s1
       then if s2
            then let rec f p x0 =
                   match p with
                   | Coq_xI p0 ->
                     (match x0 with
                      | Coq_xI p3 -> f p0 p3
                      | _ -> false)
                   | Coq_xO p0 ->
                     (match x0 with
                      | Coq_xO p3 -> f p0 p3
                      | _ -> false)
                   | Coq_xH -> (match x0 with
                                | Coq_xH -> true
                                | _ -> false)
                 in f p1 p2
            else false
       else if s2
            then false
            else let rec f p x0 =
                   match p with
                   | Coq_xI p0 ->
                     (match x0 with
                      | Coq_xI p3 -> f p0 p3
                      | _ -> false)
                   | Coq_xO p0 ->
                     (match x0 with
                      | Coq_xO p3 -> f p0 p3
                      | _ -> false)
                   | Coq_xH -> (match x0 with
                                | Coq_xH -> true
                                | _ -> false)
                 in f p1 p2
     | _ -> false)
  | Binary.B754_finite (s1, m1, e1) ->
    (match f2 with
     | Binary.B754_finite (s2, m2, e2) ->
       if s1
       then if s2
            then let s =
                   let rec f p x0 =
                     match p with
                     | Coq_xI p0 ->
                       (match x0 with
                        | Coq_xI p1 -> f p0 p1
                        | _ -> false)
                     | Coq_xO p0 ->
                       (match x0 with
                        | Coq_xO p1 -> f p0 p1
                        | _ -> false)
                     | Coq_xH -> (match x0 with
                                  | Coq_xH -> true
                                  | _ -> false)
                   in f m1 m2
                 in
                 if s then Z.eq_dec e1 e2 else false
            else false
       else if s2
            then false
            else let s =
                   let rec f p x0 =
                     match p with
                     | Coq_xI p0 ->
                       (match x0 with
                        | Coq_xI p1 -> f p0 p1
                        | _ -> false)
                     | Coq_xO p0 ->
                       (match x0 with
                        | Coq_xO p1 -> f p0 p1
                        | _ -> false)
                     | Coq_xH -> (match x0 with
                                  | Coq_xH -> true
                                  | _ -> false)
                   in f m1 m2
                 in
                 if s then Z.eq_dec e1 e2 else false
     | _ -> false)

(** val coq_BofZ : coq_Z -> coq_Z -> coq_Z -> Binary.binary_float **)

let coq_BofZ prec emax n =
  Binary.binary_normalize prec emax Coq_mode_NE n Z0 false

(** val coq_ZofB : coq_Z -> coq_Z -> Binary.binary_float -> coq_Z option **)

let coq_ZofB _ _ = function
| Binary.B754_zero _ -> Some Z0
| Binary.B754_finite (s, m, e0) ->
  (match e0 with
   | Z0 -> Some (cond_Zopp s (Zpos m))
   | Zpos e ->
     Some (Z.mul (cond_Zopp s (Zpos m)) (Z.pow_pos (radix_val radix2) e))
   | Zneg e ->
     Some (cond_Zopp s (Z.div (Zpos m) (Z.pow_pos (radix_val radix2) e))))
| _ -> None

(** val coq_ZofB_range :
    coq_Z -> coq_Z -> Binary.binary_float -> coq_Z -> coq_Z -> coq_Z option **)

let coq_ZofB_range prec emax f zmin zmax =
  match coq_ZofB prec emax f with
  | Some z -> if (&&) (Z.leb zmin z) (Z.leb z zmax) then Some z else None
  | None -> None

(** val coq_Bexact_inverse_mantissa : coq_Z -> positive **)

let coq_Bexact_inverse_mantissa prec =
  Z.iter (Z.sub prec (Zpos Coq_xH)) (fun x -> Coq_xO x) Coq_xH

(** val coq_Bexact_inverse :
    coq_Z -> coq_Z -> Binary.binary_float -> Binary.binary_float option **)

let coq_Bexact_inverse prec emax = function
| Binary.B754_finite (s, m, e) ->
  if let rec f0 p x0 =
       match p with
       | Coq_xI p0 -> (match x0 with
                       | Coq_xI p1 -> f0 p0 p1
                       | _ -> false)
       | Coq_xO p0 -> (match x0 with
                       | Coq_xO p1 -> f0 p0 p1
                       | _ -> false)
       | Coq_xH -> (match x0 with
                    | Coq_xH -> true
                    | _ -> false)
     in f0 m (coq_Bexact_inverse_mantissa prec)
  then let e' =
         Z.sub (Z.opp e)
           (Z.mul (Z.sub prec (Zpos Coq_xH)) (Zpos (Coq_xO Coq_xH)))
       in
       if coq_Z_le_dec (emin prec emax) e'
       then if coq_Z_le_dec e' emax
            then Some (Binary.B754_finite (s, m, e'))
            else None
       else None
  else None
| _ -> None

(** val pos_pow : positive -> positive -> positive **)

let rec pos_pow x = function
| Coq_xI y0 -> Pos.mul x (Pos.square (pos_pow x y0))
| Coq_xO y0 -> Pos.square (pos_pow x y0)
| Coq_xH -> x

(** val coq_Bparse :
    coq_Z -> coq_Z -> positive -> positive -> coq_Z -> Binary.binary_float **)

let coq_Bparse prec emax base m e = match e with
| Z0 -> coq_BofZ prec emax (Zpos m)
| Zpos p ->
  if Z.ltb (Z.mul e (Z.log2 (Zpos base))) emax
  then coq_BofZ prec emax (Z.mul (Zpos m) (Zpos (pos_pow base p)))
  else Binary.B754_infinity false
| Zneg p ->
  if Z.ltb (Z.add (Z.mul e (Z.log2 (Zpos base))) (Z.log2_up (Zpos m)))
       (emin prec emax)
  then Binary.B754_zero false
  else coq_BSN2B' prec emax
         (coq_SF2B prec emax
           (let (p0, lz) =
              coq_SFdiv_core_binary prec emax (Zpos m) Z0 (Zpos
                (pos_pow base p)) Z0
            in
            let (mz, ez) = p0 in
            binary_round_aux prec emax Coq_mode_NE (xorb false false) mz ez lz))

(** val coq_Bconv :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> (Binary.binary_float ->
    Binary.binary_float) -> mode -> Binary.binary_float -> Binary.binary_float **)

let coq_Bconv _ _ prec2 emax2 conv_nan md f = match f with
| Binary.B754_nan (_, _) -> build_nan prec2 emax2 (conv_nan f)
| Binary.B754_finite (s, m, e) ->
  Binary.binary_normalize prec2 emax2 md (cond_Zopp s (Zpos m)) e s
| x -> x
