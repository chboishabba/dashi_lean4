import Mathlib

/-!
# Generic setoid constructive-real → standard-real interpretation

Lean-side owner of the same application-neutral transport seam formalised in

`DASHI.Analysis.ConstructiveRealToStandardRealExact`.

The source carrier is quotient-free and carries an explicit setoid.  The target
is an abstract standard-real/transcendental algebra.  Ordinary transport asks
only that the interpretation respect source extensional equality and preserve
the operations used by analytic consumers.

Raw-representative injectivity is deliberately *not* part of the primitive
contract.  Same-object faithfulness is a separate optional strengthening.
-/

namespace Integration.ConstructiveRealToStandardReal

universe u v

/-- Minimal setoid real/algebra carrier required by the cross-prover seam. -/
structure SetoidRealCore where
  Carrier : Type u
  setoid : Setoid Carrier
  zero one : Carrier
  add sub mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier

/-- Extensional equality of the source carrier. -/
def Equivalent (R : SetoidRealCore) : R.Carrier → R.Carrier → Prop :=
  R.setoid.r

/-- Transcendental structure carried by the source setoid real. -/
structure SetoidRealTranscendental (R : SetoidRealCore) where
  exp sin cos : R.Carrier → R.Carrier
  pi : R.Carrier
  exp_congr : ∀ {x y}, Equivalent R x y → Equivalent R (exp x) (exp y)
  sin_congr : ∀ {x y}, Equivalent R x y → Equivalent R (sin x) (sin y)
  cos_congr : ∀ {x y}, Equivalent R x y → Equivalent R (cos x) (cos y)

/-- Abstract target standard-real/transcendental algebra. -/
structure StandardRealTranscendental where
  Carrier : Type v
  zero one pi : Carrier
  add sub mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  exp sin cos : Carrier → Carrier

/-- Primitive interpretation from a setoid real into a standard-real target. -/
structure StandardRealInterpretation
    (R : SetoidRealCore)
    (A : SetoidRealTranscendental R)
    (T : StandardRealTranscendental) where
  mapR : R.Carrier → T.Carrier

  respectsEquivalent :
    ∀ {x y}, Equivalent R x y → mapR x = mapR y

  preservesZero :
    mapR R.zero = T.zero

  preservesOne :
    mapR R.one = T.one

  preservesAdd :
    ∀ x y, mapR (R.add x y) = T.add (mapR x) (mapR y)

  preservesSub :
    ∀ x y, mapR (R.sub x y) = T.sub (mapR x) (mapR y)

  preservesMul :
    ∀ x y, mapR (R.mul x y) = T.mul (mapR x) (mapR y)

  preservesNeg :
    ∀ x, mapR (R.neg x) = T.neg (mapR x)

  preservesExp :
    ∀ x, mapR (A.exp x) = T.exp (mapR x)

  preservesSin :
    ∀ x, mapR (A.sin x) = T.sin (mapR x)

  preservesCos :
    ∀ x, mapR (A.cos x) = T.cos (mapR x)

  preservesPi :
    mapR A.pi = T.pi

/-- Optional same-object faithfulness.  It is intentionally separate from
ordinary transport. -/
structure FaithfulStandardRealInterpretation
    {R : SetoidRealCore}
    {A : SetoidRealTranscendental R}
    {T : StandardRealTranscendental}
    (I : StandardRealInterpretation R A T) where
  reflectsEquivalent :
    ∀ {x y}, I.mapR x = I.mapR y → Equivalent R x y

/-- Componentwise complex carrier over the target real algebra. -/
structure StandardComplex (T : StandardRealTranscendental) where
  re im : T.Carrier
  deriving DecidableEq

/-- Componentwise complex transport induced by a real interpretation. -/
def mapComplex
    {R : SetoidRealCore}
    {A : SetoidRealTranscendental R}
    {T : StandardRealTranscendental}
    (I : StandardRealInterpretation R A T)
    (x y : R.Carrier) :
    StandardComplex T :=
  ⟨I.mapR x, I.mapR y⟩

/-- Source extensional equality in both components descends to equality of the
transported complex value. -/
theorem mapComplex_equivalent
    {R : SetoidRealCore}
    {A : SetoidRealTranscendental R}
    {T : StandardRealTranscendental}
    (I : StandardRealInterpretation R A T)
    {xr xi yr yi : R.Carrier}
    (hre : Equivalent R xr yr)
    (him : Equivalent R xi yi) :
    mapComplex I xr xi = mapComplex I yr yi := by
  cases I.respectsEquivalent hre
  cases I.respectsEquivalent him
  rfl

/-- Machine-readable boundary status for the shared seam. -/
structure ConstructiveRealToStandardRealBoundary where
  setoidRespectRequired : Bool
  rawRepresentativeInjectivityRequired : Bool
  faithfulnessSeparatedFromTransport : Bool
  deriving DecidableEq, Repr

/-- Canonical repository policy: respect the quotient/setoid; do not demand
injectivity of raw representatives; keep faithfulness as an optional layer. -/
def canonicalBoundary : ConstructiveRealToStandardRealBoundary :=
  ⟨true, false, true⟩

theorem canonicalBoundary_setoidRespect :
    canonicalBoundary.setoidRespectRequired = true := rfl

theorem canonicalBoundary_noRawInjectivity :
    canonicalBoundary.rawRepresentativeInjectivityRequired = false := rfl

theorem canonicalBoundary_faithfulnessSeparated :
    canonicalBoundary.faithfulnessSeparatedFromTransport = true := rfl

end Integration.ConstructiveRealToStandardReal
