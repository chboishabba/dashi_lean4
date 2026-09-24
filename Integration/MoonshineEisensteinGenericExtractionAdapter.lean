import Integration.ConstructiveRealStandardExtraction
import Integration.MoonshineEisensteinPrimitiveExtraction

/-!
# Adapter: generic constructive-real extraction feeds the Moonshine compiler

The application-specific Moonshine transport layer predates the generic
`ConstructiveRealStandardExtraction` owner.  This file provides the only
adapter needed between them.  No second primitive interpretation is required:
an inhabitant of the generic extraction record canonically produces the
Moonshine extraction package and therefore all existing q/E4/E6 transport.
-/

namespace Integration.MoonshineEisensteinGenericExtractionAdapter

namespace G := Integration.ConstructiveRealStandardExtraction
namespace M := Integration.MoonshineEisensteinPrimitiveExtraction

noncomputable section

def toMoonshineReal (S : G.SourceRealTranscendental) : M.SourceRealTranscendental where
  Carrier := S.Carrier
  equiv := S.equiv
  zero := S.zero
  one := S.one
  add := S.add
  sub := S.sub
  mul := S.mul
  neg := S.neg
  exp := S.exp
  sin := S.sin
  cos := S.cos
  pi := S.pi

def toMoonshineComplex
    {S : G.SourceRealTranscendental} :
    G.SourceComplex S → M.SourceComplex (toMoonshineReal S)
  | ⟨x,y⟩ => ⟨x,y⟩

def fromMoonshineComplex
    {S : G.SourceRealTranscendental} :
    M.SourceComplex (toMoonshineReal S) → G.SourceComplex S
  | ⟨x,y⟩ => ⟨x,y⟩

@[simp] theorem from_to_complex
    {S : G.SourceRealTranscendental} (z : G.SourceComplex S) :
    fromMoonshineComplex (toMoonshineComplex z) = z := by
  cases z <;> rfl

@[simp] theorem to_from_complex
    {S : G.SourceRealTranscendental}
    (z : M.SourceComplex (toMoonshineReal S)) :
    toMoonshineComplex (fromMoonshineComplex z) = z := by
  cases z <;> rfl

def toMoonshinePackage (P : G.SourceComplexPackage) : M.SourceComplexPackage where
  real := toMoonshineReal P.real
  expC := fun z => toMoonshineComplex (P.expC (fromMoonshineComplex z))
  expCartesian := by
    intro z
    apply M.SourceComplex.ext <;>
      simp [toMoonshineComplex,fromMoonshineComplex,
        G.SourceComplex.expCartesian,M.SourceComplex.expCartesian,
        P.expCartesian]

def toMoonshineExtraction
    {S : G.SourceRealTranscendental}
    (E : G.PrimitiveRealExtraction S) :
    M.PrimitiveRealExtraction (toMoonshineReal S) where
  map := E.map
  respects_equiv := E.respects_equiv
  map_zero := E.map_zero
  map_one := E.map_one
  map_add := E.map_add
  map_sub := E.map_sub
  map_mul := E.map_mul
  map_neg := E.map_neg
  map_exp := E.map_exp
  map_sin := E.map_sin
  map_cos := E.map_cos
  map_pi := E.map_pi

def toMoonshineFaithful
    {S : G.SourceRealTranscendental}
    {E : G.PrimitiveRealExtraction S}
    (F : G.FaithfulPrimitiveRealExtraction S E) :
    M.FaithfulPrimitiveRealExtraction
      (toMoonshineReal S) (toMoonshineExtraction E) where
  reflects_equiv := F.reflects_equiv

theorem genericExtraction_compiles_moonshineQ
    {P : G.SourceComplexPackage}
    (E : G.PrimitiveRealExtraction P.real)
    (τ : G.SourceComplex P.real) :
    M.mapComplex (P := toMoonshinePackage P) (toMoonshineExtraction E)
      (M.sourceQ (toMoonshinePackage P) (toMoonshineComplex τ)) =
      Complex.exp (((2 : ℂ) * (Complex.I * Real.pi)) *
        M.mapComplex (P := toMoonshinePackage P) (toMoonshineExtraction E)
          (toMoonshineComplex τ)) := by
  exact M.map_sourceQ (P := toMoonshinePackage P)
    (toMoonshineExtraction E) (toMoonshineComplex τ)

theorem genericExtraction_compiles_moonshineE4
    {P : G.SourceComplexPackage}
    (E : G.PrimitiveRealExtraction P.real)
    (N : ℕ) (q : G.SourceComplex P.real) :
    M.mapComplex (P := toMoonshinePackage P) (toMoonshineExtraction E)
      (M.sourceE4 (P := toMoonshinePackage P) N (toMoonshineComplex q)) =
      Integration.MoonshineEisensteinAgdaTarget.e4TruncatedTarget N
        (M.mapComplex (P := toMoonshinePackage P) (toMoonshineExtraction E)
          (toMoonshineComplex q)) := by
  exact M.map_sourceE4 (P := toMoonshinePackage P)
    (toMoonshineExtraction E) N (toMoonshineComplex q)

theorem genericExtraction_compiles_moonshineE6
    {P : G.SourceComplexPackage}
    (E : G.PrimitiveRealExtraction P.real)
    (N : ℕ) (q : G.SourceComplex P.real) :
    M.mapComplex (P := toMoonshinePackage P) (toMoonshineExtraction E)
      (M.sourceE6 (P := toMoonshinePackage P) N (toMoonshineComplex q)) =
      Integration.MoonshineEisensteinAgdaTarget.e6TruncatedTarget N
        (M.mapComplex (P := toMoonshinePackage P) (toMoonshineExtraction E)
          (toMoonshineComplex q)) := by
  exact M.map_sourceE6 (P := toMoonshinePackage P)
    (toMoonshineExtraction E) N (toMoonshineComplex q)

end

end Integration.MoonshineEisensteinGenericExtractionAdapter
