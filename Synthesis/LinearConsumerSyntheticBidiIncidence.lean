import Synthesis.LinearConsumerPreparedOperator

/-!
# Exact finite synthetic bidi incidence mirror

This file mirrors the deterministic finite incidence constructor used by the
`dashiRTX` synthetic RSA-260 Block-Wiedemann baseline.

Runtime construction:

* rows = 924, cols = 512;
* row degree is 151 for rows 0..5 and 150 otherwise;
* row base is `(2654435761 * r + 0x9e3779b9) mod 512`;
* support is the cyclic interval of `degree(r)` consecutive columns starting at
  `base(r)`.

The dashiRTX runtime independently checks that this extensional modular-distance
formula matches its original `build_A()` constructor entrywise on all
924×512 cells.  This Lean source still does not turn that runtime check into a
cross-prover equality receipt; it simply owns the exact finite constructor on
the formal side.
-/

namespace Synthesis

abbrev SyntheticBidiRows := Fin 924
abbrev SyntheticBidiCols := Fin 512
abbrev SyntheticBidiBlock := Fin 8

/-- Runtime row degree: six rows of degree 151, then degree 150. -/
def syntheticBidiRowDegree (r : SyntheticBidiRows) : Nat :=
  if r.val < 6 then 151 else 150

/-- Runtime affine cyclic support base. -/
def syntheticBidiRowBase (r : SyntheticBidiRows) : Nat :=
  (r.val * 2654435761 + 0x9E3779B9) % 512

/-- Extensional form of the finite runtime incidence matrix over GF(2). -/
def syntheticBidiIncidence :
    Matrix SyntheticBidiRows SyntheticBidiCols (ZMod 2) :=
  fun r c =>
    if ((c.val + 512 - syntheticBidiRowBase r) % 512 < syntheticBidiRowDegree r)
    then 1
    else 0

@[simp]
theorem syntheticBidiIncidence_apply
    (r : SyntheticBidiRows) (c : SyntheticBidiCols) :
    syntheticBidiIncidence r c =
      if ((c.val + 512 - syntheticBidiRowBase r) % 512 < syntheticBidiRowDegree r)
      then 1
      else 0 :=
  rfl

/-- Formal prepared operator for the mirrored synthetic incidence matrix. -/
def syntheticBidiPreparedOperator :
    Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) →ₗ[ZMod 2]
      Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  gramPreparedOperator syntheticBidiIncidence

@[simp]
theorem syntheticBidiPreparedOperator_apply
    (Y : Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2)) :
    syntheticBidiPreparedOperator Y =
      syntheticBidiIncidence * (syntheticBidiIncidence.transpose * Y) :=
  gramPreparedOperator_apply syntheticBidiIncidence Y

end Synthesis
