import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Generic setoid real/transcendental extraction into Lean Real

Repository-wide owner for the primitive cross-prover real seam.

The source carrier is intentionally abstract and setoid-valued.  Transport
requires only that equivalent source representatives map to the same Lean real
and that the selected ring/transcendental primitives are preserved.

Raw representative injectivity is deliberately absent.  Optional same-object
faithfulness is a separate strengthening.
-/

namespace Integration.ConstructiveRealStandardExtraction

open Complex Real

noncomputable section

structure SourceRealTranscendental where
  Carrier : Type
  equiv : Carrier → Carrier → Prop
  zero one : Carrier
  add sub mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  exp sin cos : Carrier → Carrier
  pi : Carrier

structure SourceComplex (S : SourceRealTranscendental) where
  re : S.Carrier
  im : S.Carrier

namespace SourceComplex

variable {S : SourceRealTranscendental}

def zero : SourceComplex S := ⟨S.zero,S.zero⟩
def one : SourceComplex S := ⟨S.one,S.zero⟩
def I : SourceComplex S := ⟨S.zero,S.one⟩
def pi : SourceComplex S := ⟨S.pi,S.zero⟩

def add (x y : SourceComplex S) : SourceComplex S :=
  ⟨S.add x.re y.re,S.add x.im y.im⟩

def sub (x y : SourceComplex S) : SourceComplex S :=
  ⟨S.sub x.re y.re,S.sub x.im y.im⟩

def mul (x y : SourceComplex S) : SourceComplex S :=
  ⟨S.sub (S.mul x.re y.re) (S.mul x.im y.im),
   S.add (S.mul x.re y.im) (S.mul x.im y.re)⟩

def expCartesian (z : SourceComplex S) : SourceComplex S :=
  ⟨S.mul (S.exp z.re) (S.cos z.im),
   S.mul (S.exp z.re) (S.sin z.im)⟩

end SourceComplex

structure SourceComplexPackage where
  real : SourceRealTranscendental
  expC : SourceComplex real → SourceComplex real
  expCartesian : ∀ z, expC z = SourceComplex.expCartesian z

structure PrimitiveRealExtraction (S : SourceRealTranscendental) where
  map : S.Carrier → ℝ
  respects_equiv : ∀ {x y}, S.equiv x y → map x = map y
  map_zero : map S.zero = 0
  map_one : map S.one = 1
  map_add : ∀ x y, map (S.add x y) = map x + map y
  map_sub : ∀ x y, map (S.sub x y) = map x - map y
  map_mul : ∀ x y, map (S.mul x y) = map x * map y
  map_neg : ∀ x, map (S.neg x) = -map x
  map_exp : ∀ x, map (S.exp x) = Real.exp (map x)
  map_sin : ∀ x, map (S.sin x) = Real.sin (map x)
  map_cos : ∀ x, map (S.cos x) = Real.cos (map x)
  map_pi : map S.pi = Real.pi

structure FaithfulPrimitiveRealExtraction
    (S : SourceRealTranscendental)
    (E : PrimitiveRealExtraction S) : Prop where
  reflects_equiv : ∀ {x y}, E.map x = E.map y → S.equiv x y

variable {P : SourceComplexPackage}

def mapComplex (E : PrimitiveRealExtraction P.real)
    (z : SourceComplex P.real) : ℂ :=
  ⟨E.map z.re,E.map z.im⟩

@[simp] theorem mapComplex_zero (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.zero = 0 := by
  ext <;> simp [mapComplex,SourceComplex.zero,E.map_zero]

@[simp] theorem mapComplex_one (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.one = 1 := by
  ext <;> simp [mapComplex,SourceComplex.one,E.map_zero,E.map_one]

@[simp] theorem mapComplex_I (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.I = Complex.I := by
  ext <;> simp [mapComplex,SourceComplex.I,E.map_zero,E.map_one]

@[simp] theorem mapComplex_add
    (E : PrimitiveRealExtraction P.real)
    (x y : SourceComplex P.real) :
    mapComplex E (SourceComplex.add x y) = mapComplex E x + mapComplex E y := by
  ext <;> simp [mapComplex,SourceComplex.add,E.map_add]

@[simp] theorem mapComplex_sub
    (E : PrimitiveRealExtraction P.real)
    (x y : SourceComplex P.real) :
    mapComplex E (SourceComplex.sub x y) = mapComplex E x - mapComplex E y := by
  ext <;> simp [mapComplex,SourceComplex.sub,E.map_sub]

@[simp] theorem mapComplex_mul
    (E : PrimitiveRealExtraction P.real)
    (x y : SourceComplex P.real) :
    mapComplex E (SourceComplex.mul x y) = mapComplex E x * mapComplex E y := by
  ext <;> simp [mapComplex,SourceComplex.mul,E.map_add,E.map_sub,E.map_mul] <;> ring

theorem mapComplex_exp
    (E : PrimitiveRealExtraction P.real)
    (z : SourceComplex P.real) :
    mapComplex E (P.expC z) = Complex.exp (mapComplex E z) := by
  rw [P.expCartesian]
  ext
  · simp [mapComplex,SourceComplex.expCartesian,E.map_mul,E.map_exp,E.map_cos,Complex.exp_re]
  · simp [mapComplex,SourceComplex.expCartesian,E.map_mul,E.map_exp,E.map_sin,Complex.exp_im]

structure ExtractionBoundary where
  setoidRespectRequired : Bool
  rawRepresentativeInjectivityRequired : Bool
  faithfulnessSeparate : Bool
  actualCrossProverInterpretationInhabited : Bool

def extractionBoundary : ExtractionBoundary where
  setoidRespectRequired := true
  rawRepresentativeInjectivityRequired := false
  faithfulnessSeparate := true
  actualCrossProverInterpretationInhabited := false

end

end Integration.ConstructiveRealStandardExtraction
