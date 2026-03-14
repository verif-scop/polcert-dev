open BinInt
open BinNums
open BinPos
open Datatypes
open Zbool
open Zpower

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * coq_Z

(** val emin : coq_Z -> coq_Z -> coq_Z **)

let emin prec emax =
  Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec

(** val fexp : coq_Z -> coq_Z -> coq_Z -> coq_Z **)

let fexp prec emax e =
  Z.max (Z.sub e prec) (emin prec emax)

(** val digits2_pos : positive -> positive **)

let rec digits2_pos = function
| Coq_xI p -> Pos.succ (digits2_pos p)
| Coq_xO p -> Pos.succ (digits2_pos p)
| Coq_xH -> Coq_xH

(** val coq_Zdigits2 : coq_Z -> coq_Z **)

let coq_Zdigits2 n = match n with
| Z0 -> n
| Zpos p -> Zpos (digits2_pos p)
| Zneg p -> Zpos (digits2_pos p)

(** val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  match n with
  | Coq_xI n' -> iter_pos f n' (iter_pos f n' (f x))
  | Coq_xO n' -> iter_pos f n' (iter_pos f n' x)
  | Coq_xH -> f x

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zpos p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zpos p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zneg p); shr_r = true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zneg p); shr_r = false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = true; shr_s = s0 }))

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Coq_loc_Inexact Gt else Coq_loc_Inexact Eq
  else if shr_s0 then Coq_loc_Inexact Lt else Coq_loc_Exact

(** val shr_record_of_loc : coq_Z -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> coq_Z -> coq_Z -> shr_record * coq_Z **)

let shr mrs e n = match n with
| Zpos p -> ((iter_pos shr_1 p mrs), (Z.add e n))
| _ -> (mrs, e)

(** val shr_fexp :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> shr_record * coq_Z **)

let shr_fexp prec emax m e l =
  shr (shr_record_of_loc m l) e
    (Z.sub (fexp prec emax (Z.add (coq_Zdigits2 m) e)) e)

(** val shl_align : positive -> coq_Z -> coq_Z -> positive * coq_Z **)

let shl_align mx ex ex' =
  match Z.sub ex' ex with
  | Zneg d -> ((shift_pos d mx), ex')
  | _ -> (mx, ex)

(** val coq_SFcompare : spec_float -> spec_float -> comparison option **)

let coq_SFcompare f1 f2 =
  match f1 with
  | S754_zero _ ->
    (match f2 with
     | S754_zero _ -> Some Eq
     | S754_infinity s -> Some (if s then Gt else Lt)
     | S754_nan -> None
     | S754_finite (s, _, _) -> Some (if s then Gt else Lt))
  | S754_infinity s ->
    (match f2 with
     | S754_infinity s0 ->
       Some (if s then if s0 then Eq else Lt else if s0 then Gt else Eq)
     | S754_nan -> None
     | _ -> Some (if s then Lt else Gt))
  | S754_nan -> None
  | S754_finite (s1, m1, e1) ->
    (match f2 with
     | S754_zero _ -> Some (if s1 then Lt else Gt)
     | S754_infinity s -> Some (if s then Gt else Lt)
     | S754_nan -> None
     | S754_finite (s2, m2, e2) ->
       Some
         (if s1
          then if s2
               then (match Z.compare e1 e2 with
                     | Eq -> coq_CompOpp (Pos.compare_cont Eq m1 m2)
                     | Lt -> Gt
                     | Gt -> Lt)
               else Lt
          else if s2
               then Gt
               else (match Z.compare e1 e2 with
                     | Eq -> Pos.compare_cont Eq m1 m2
                     | x -> x)))

(** val cond_Zopp : bool -> coq_Z -> coq_Z **)

let cond_Zopp b m =
  if b then Z.opp m else m

(** val new_location_even : coq_Z -> coq_Z -> location **)

let new_location_even nb_steps k =
  if coq_Zeq_bool k Z0
  then Coq_loc_Exact
  else Coq_loc_Inexact (Z.compare (Z.mul (Zpos (Coq_xO Coq_xH)) k) nb_steps)

(** val new_location_odd : coq_Z -> coq_Z -> location **)

let new_location_odd nb_steps k =
  if coq_Zeq_bool k Z0
  then Coq_loc_Exact
  else Coq_loc_Inexact
         (match Z.compare
                  (Z.add (Z.mul (Zpos (Coq_xO Coq_xH)) k) (Zpos Coq_xH))
                  nb_steps with
          | Eq -> Lt
          | x -> x)

(** val new_location : coq_Z -> coq_Z -> location **)

let new_location nb_steps =
  if Z.even nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps

(** val coq_SFdiv_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z ->
    (coq_Z * coq_Z) * location **)

let coq_SFdiv_core_binary prec emax m1 e1 m2 e2 =
  let d1 = coq_Zdigits2 m1 in
  let d2 = coq_Zdigits2 m2 in
  let e' =
    Z.min (fexp prec emax (Z.sub (Z.add d1 e1) (Z.add d2 e2))) (Z.sub e1 e2)
  in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' = match s with
           | Z0 -> m1
           | Zpos _ -> Z.shiftl m1 s
           | Zneg _ -> Z0 in
  let (q, r) = Z.div_eucl m' m2 in ((q, e'), (new_location m2 r))

(** val coq_SFsqrt_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) * location **)

let coq_SFsqrt_core_binary prec emax m e =
  let d = coq_Zdigits2 m in
  let e' =
    Z.min (fexp prec emax (Z.div2 (Z.add (Z.add d e) (Zpos Coq_xH))))
      (Z.div2 e)
  in
  let s = Z.sub e (Z.mul (Zpos (Coq_xO Coq_xH)) e') in
  let m' = match s with
           | Z0 -> m
           | Zpos _ -> Z.shiftl m s
           | Zneg _ -> Z0 in
  let (q, r) = Z.sqrtrem m' in
  let l =
    if coq_Zeq_bool r Z0
    then Coq_loc_Exact
    else Coq_loc_Inexact (if Z.leb r q then Lt else Gt)
  in
  ((q, e'), l)
