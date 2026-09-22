import Integration.MoonshineEisensteinAgdaTarget

/-!
# Primitive real/transcendental extraction contract for the Agda Eisenstein lane

This Lean module mirrors the data required by

  DASHI.Moonshine.JInvariantEisensteinAgdaLeanRealExtractionExact

on the Agda side.

The source is intentionally abstract: it is the declaration-level shape that a
future Agda mirror / generated interface must instantiate.  No claim is made
that the current Agda carrier has already been imported into Lean.

The key point is structural: a map from the source real carrier into Lean Real
that preserves 0, 1, +, -, *, neg, exp, sin, cos and pi induces a componentwise
map from the source ComplexPair into Lean Complex.  The source Cartesian
complex-exponential law then gives preservation of complex exp, and the literal
Agda-shaped q/E4/E6 recurrences transport by induction.
-/

namespace Integration.MoonshineEisensteinPrimitiveExtraction

open Complex Real
open ArithmeticFunction
open scoped Real Nat ArithmeticFunction.sigma

noncomputable section

/-- Abstract mirror of the real/transcendental fields actually consumed by
Agda's ConcreteComplex package. -/
structure SourceRealTranscendental where
  Carrier : Type
  zero one : Carrier
  add sub mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  exp sin cos : Carrier → Carrier
  pi : Carrier

/-- Source complex pair exactly matching Agda's Cartesian representation. -/
structure SourceComplex (S : SourceRealTranscendental) where
  re : S.Carrier
  im : S.Carrier

namespace SourceComplex

variable {S : SourceRealTranscendental}

def zero : SourceComplex S := ⟨S.zero, S.zero⟩
def one : SourceComplex S := ⟨S.one, S.zero⟩
def I : SourceComplex S := ⟨S.zero, S.one⟩
def pi : SourceComplex S := ⟨S.pi, S.zero⟩

def add (x y : SourceComplex S) : SourceComplex S :=
  ⟨S.add x.re y.re, S.add x.im y.im⟩

def sub (x y : SourceComplex S) : SourceComplex S :=
  ⟨S.sub x.re y.re, S.sub x.im y.im⟩

def mul (x y : SourceComplex S) : SourceComplex S :=
  ⟨S.sub (S.mul x.re y.re) (S.mul x.im y.im),
   S.add (S.mul x.re y.im) (S.mul x.im y.re)⟩

def expCartesian (z : SourceComplex S) : SourceComplex S :=
  ⟨S.mul (S.exp z.re) (S.cos z.im),
   S.mul (S.exp z.re) (S.sin z.im)⟩

end SourceComplex

/-- The actual source package may have a separately implemented complex
exponential, provided it is propositionally equal to the Cartesian formula. -/
structure SourceComplexPackage where
  real : SourceRealTranscendental
  expC : SourceComplex real → SourceComplex real
  expCartesian : ∀ z, expC z = SourceComplex.expCartesian z

/-- Primitive faithful interpretation into Lean Real.  Injectivity is retained
because route B ultimately wants a same-object embedding rather than merely a
homomorphic collapse. -/
structure PrimitiveRealExtraction (S : SourceRealTranscendental) where
  map : S.Carrier → ℝ
  injective : Function.Injective map

  map_zero : map S.zero = 0
  map_one : map S.one = 1
  map_add : ∀ x y, map (S.add x y) = map x + map y
  map_sub : ∀ x y, map (S.sub x y) = map x - map y
  map_mul : ∀ x y, map (S.mul x y) = map x * map y
  map_neg : ∀ x, map (S.neg x) = - map x

  map_exp : ∀ x, map (S.exp x) = Real.exp (map x)
  map_sin : ∀ x, map (S.sin x) = Real.sin (map x)
  map_cos : ∀ x, map (S.cos x) = Real.cos (map x)
  map_pi : map S.pi = Real.pi

variable {P : SourceComplexPackage}

/-- Componentwise induced map into Lean Complex. -/
def mapComplex (E : PrimitiveRealExtraction P.real)
    (z : SourceComplex P.real) : ℂ :=
  ⟨E.map z.re, E.map z.im⟩

@[simp] theorem mapComplex_zero
    (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.zero = 0 := by
  ext <;> simp [mapComplex, SourceComplex.zero, E.map_zero]

@[simp] theorem mapComplex_one
    (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.one = 1 := by
  ext <;> simp [mapComplex, SourceComplex.one, E.map_zero, E.map_one]

@[simp] theorem mapComplex_I
    (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.I = Complex.I := by
  ext <;> simp [mapComplex, SourceComplex.I, E.map_zero, E.map_one]

@[simp] theorem mapComplex_pi
    (E : PrimitiveRealExtraction P.real) :
    mapComplex E SourceComplex.pi = (Real.pi : ℂ) := by
  ext <;> simp [mapComplex, SourceComplex.pi, E.map_zero, E.map_pi]

@[simp] theorem mapComplex_add
    (E : PrimitiveRealExtraction P.real)
    (x y : SourceComplex P.real) :
    mapComplex E (SourceComplex.add x y) =
      mapComplex E x + mapComplex E y := by
  ext <;> simp [mapComplex, SourceComplex.add, E.map_add]

@[simp] theorem mapComplex_sub
    (E : PrimitiveRealExtraction P.real)
    (x y : SourceComplex P.real) :
    mapComplex E (SourceComplex.sub x y) =
      mapComplex E x - mapComplex E y := by
  ext <;> simp [mapComplex, SourceComplex.sub, E.map_sub]

@[simp] theorem mapComplex_mul
    (E : PrimitiveRealExtraction P.real)
    (x y : SourceComplex P.real) :
    mapComplex E (SourceComplex.mul x y) =
      mapComplex E x * mapComplex E y := by
  ext <;>
    simp [mapComplex, SourceComplex.mul, E.map_add, E.map_sub, E.map_mul] <;>
    ring

/-- Complex exponential preservation is derived from the source Cartesian law
and the primitive real transcendental preservation fields. -/
theorem mapComplex_exp
    (E : PrimitiveRealExtraction P.real)
    (z : SourceComplex P.real) :
    mapComplex E (P.expC z) = Complex.exp (mapComplex E z) := by
  rw [P.expCartesian]
  ext
  · simp [mapComplex, SourceComplex.expCartesian,
      E.map_mul, E.map_exp, E.map_cos, Complex.exp_re]
  · simp [mapComplex, SourceComplex.expCartesian,
      E.map_mul, E.map_exp, E.map_sin, Complex.exp_im]

/-- Repeated addition used by the literal Agda finite recurrences. -/
def sourceScaleNat (S : SourceRealTranscendental) :
    ℕ → SourceComplex S → SourceComplex S
  | 0, _ => SourceComplex.zero
  | n + 1, z => SourceComplex.add z (sourceScaleNat S n z)

def sourcePow (S : SourceRealTranscendental)
    (z : SourceComplex S) : ℕ → SourceComplex S
  | 0 => SourceComplex.one
  | n + 1 => SourceComplex.mul z (sourcePow S z n)

@[simp] theorem map_sourceScaleNat
    (E : PrimitiveRealExtraction P.real)
    (n : ℕ) (z : SourceComplex P.real) :
    mapComplex E (sourceScaleNat P.real n z) =
      Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget n
        (mapComplex E z) := by
  induction n with
  | zero =>
      simp [sourceScaleNat,
        Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget]
  | succ n ih =>
      simp [sourceScaleNat, ih,
        Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget]
      ring

@[simp] theorem map_sourcePow
    (E : PrimitiveRealExtraction P.real)
    (z : SourceComplex P.real) (n : ℕ) :
    mapComplex E (sourcePow P.real z n) = mapComplex E z ^ n := by
  induction n with
  | zero => simp [sourcePow]
  | succ n ih =>
      simp [sourcePow, ih, pow_succ]

/-- Literal source q, matching the Agda parenthesization. -/
def sourceQ (P : SourceComplexPackage) (τ : SourceComplex P.real) :
    SourceComplex P.real :=
  P.expC
    (SourceComplex.mul
      (sourceScaleNat P.real 2
        (SourceComplex.mul SourceComplex.I SourceComplex.pi))
      τ)

theorem map_sourceQ
    (E : PrimitiveRealExtraction P.real)
    (τ : SourceComplex P.real) :
    mapComplex E (sourceQ P τ) =
      Complex.exp (((2 : ℂ) * (Complex.I * Real.pi)) * mapComplex E τ) := by
  simp [sourceQ, mapComplex_exp, map_sourceScaleNat]
  ring_nf

/-- Literal source E4 recurrence. -/
def sourceE4 : ℕ → SourceComplex P.real → SourceComplex P.real
  | 0, _ => SourceComplex.one
  | n + 1, q =>
      SourceComplex.add
        (sourceE4 n q)
        (sourceScaleNat P.real (240 * σ 3 (n + 1))
          (sourcePow P.real q (n + 1)))

/-- Literal source E6 recurrence. -/
def sourceE6 : ℕ → SourceComplex P.real → SourceComplex P.real
  | 0, _ => SourceComplex.one
  | n + 1, q =>
      SourceComplex.sub
        (sourceE6 n q)
        (sourceScaleNat P.real (504 * σ 5 (n + 1))
          (sourcePow P.real q (n + 1)))

theorem map_sourceE4
    (E : PrimitiveRealExtraction P.real)
    (N : ℕ) (q : SourceComplex P.real) :
    mapComplex E (sourceE4 (P := P) N q) =
      Integration.MoonshineEisensteinAgdaTarget.e4TruncatedTarget N
        (mapComplex E q) := by
  induction N with
  | zero => simp [sourceE4]
  | succ N ih =>
      simp [sourceE4,
        Integration.MoonshineEisensteinAgdaTarget.e4TruncatedTarget,
        ih, map_sourceScaleNat, map_sourcePow]

theorem map_sourceE6
    (E : PrimitiveRealExtraction P.real)
    (N : ℕ) (q : SourceComplex P.real) :
    mapComplex E (sourceE6 (P := P) N q) =
      Integration.MoonshineEisensteinAgdaTarget.e6TruncatedTarget N
        (mapComplex E q) := by
  induction N with
  | zero => simp [sourceE6]
  | succ N ih =>
      simp [sourceE6,
        Integration.MoonshineEisensteinAgdaTarget.e6TruncatedTarget,
        ih, map_sourceScaleNat, map_sourcePow]

/-- Status surface: all recurrence transport is compiled from one primitive
real/transcendental extraction. -/
structure PrimitiveExtractionBoundary where
  componentwiseComplexMapOwned : Bool
  complexRingTransportOwned : Bool
  complexExpTransportOwned : Bool
  literalQTransportOwned : Bool
  literalE4TransportOwned : Bool
  literalE6TransportOwned : Bool
  actualAgdaMirrorPackageInhabited : Bool
  primitiveAgdaRealToLeanRealExtractionInhabited : Bool

def primitiveExtractionBoundary : PrimitiveExtractionBoundary where
  componentwiseComplexMapOwned := true
  complexRingTransportOwned := true
  complexExpTransportOwned := true
  literalQTransportOwned := true
  literalE4TransportOwned := true
  literalE6TransportOwned := true
  actualAgdaMirrorPackageInhabited := false
  primitiveAgdaRealToLeanRealExtractionInhabited := false

end

end Integration.MoonshineEisensteinPrimitiveExtraction
