Require Import driver.PolOpt.
Require Import src.TPolIRs.
Module P := PolOpt TPolIRs.
Definition coerce1 (x: P.PolyLang.t) : P.CheckedTiling.Tiling.PL.t := x.
Definition coerce2 (x: P.CheckedTiling.Tiling.PL.t) : P.PolyLang.t := x.
