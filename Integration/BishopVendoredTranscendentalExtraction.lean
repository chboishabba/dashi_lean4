import Integration.BishopVendoredRealEvaluation
import Integration.MoonshineEisensteinPrimitiveExtraction

/-!
# Vendored Bishop evaluator -> route-B primitive extraction

This module connects the reusable evaluator for DASHI's vendored Bishop regular
reals to the primitive extraction contract consumed by the Moonshine/Eisenstein
route.

The ring part is no longer an assumption.  Given the exact vendored arithmetic
sequence equations, evaluation into Lean Real preserves zero, one, addition,
subtraction, negation and the canonical-bound-resampled multiplication.

Only the semantic identification of the already-constructed Bishop
transcendentals remains:
* Bishop exp with Real.exp;
* Bishop sine with Real.sin;
* Bishop cosine with Real.cos;
* the selected Bishop pi object with Real.pi.

Once those four facts are supplied, the full PrimitiveRealExtraction is
constructed and the q/E4/E6/Delta reflection transport compiler is available.
-/

namespace Integration.BishopVendoredTranscendentalExtraction

open Integration.BishopVendoredRealEvaluation
open Integration.MoonshineEisensteinPrimitiveExtraction

noncomputable section

/-- Exact transcendental operations selected on the vendored Bishop carrier,
plus their remaining semantic identifications with Lean's classical functions. -/
structure VendoredTranscendentalMirror
    (A : VendoredArithmeticMirror) where
  expB sinB cosB : RegularRatReal → RegularRatReal
  piB : RegularRatReal

  eval_exp :
    ∀ x, eval (expB x) = Real.exp (eval x)

  eval_sin :
    ∀ x, eval (sinB x) = Real.sin (eval x)

  eval_cos :
    ∀ x, eval (cosB x) = Real.cos (eval x)

  eval_pi :
    eval piB = Real.pi

/-- The actual vendored algebra and chosen Bishop transcendental operations
presented in the source shape expected by the route-B compiler. -/
def bishopSourceReal
    (A : VendoredArithmeticMirror)
    (T : VendoredTranscendentalMirror A) :
    SourceRealTranscendental where
  Carrier := RegularRatReal
  equiv := Equiv
  zero := A.zero
  one := A.one
  add := A.add
  sub := fun x y => A.add x (A.neg y)
  mul := A.mul
  neg := A.neg
  exp := T.expB
  sin := T.sinB
  cos := T.cosB
  pi := T.piB

private theorem eval_sub
    (A : VendoredArithmeticMirror)
    (x y : RegularRatReal) :
    eval (A.add x (A.neg y)) = eval x - eval y := by
  rw [A.eval_add, A.eval_neg]
  ring

/-- The full route-B primitive real extraction is constructed from the vendored
arithmetic evaluator and only the four transcendental semantic theorems. -/
def primitiveExtraction
    (A : VendoredArithmeticMirror)
    (T : VendoredTranscendentalMirror A) :
    PrimitiveRealExtraction (bishopSourceReal A T) where
  map := eval

  respects_equiv := eval_respects_equiv

  map_zero := A.eval_zero
  map_one := A.eval_one
  map_add := A.eval_add
  map_sub := eval_sub A
  map_mul := A.eval_mul
  map_neg := A.eval_neg

  map_exp := T.eval_exp
  map_sin := T.eval_sin
  map_cos := T.eval_cos
  map_pi := T.eval_pi

/-- Once the selected Bishop package is mirrored, its componentwise complex
extraction into Lean Complex is automatic. -/
def complexExtraction
    (A : VendoredArithmeticMirror)
    (T : VendoredTranscendentalMirror A) :=
  Integration.MoonshineEisensteinPrimitiveExtraction.mapComplex
    (P := {
      real := bishopSourceReal A T
      expC := SourceComplex.expCartesian
      expCartesian := fun _ => rfl
    })
    (primitiveExtraction A T)

/-- Machine-readable frontier. -/
structure VendoredTranscendentalExtractionBoundary where
  vendoredArithmeticEvaluationOwned : Bool
  routeBPrimitiveExtractionCompilerOwned : Bool
  routeBComplexExtractionCompilerOwned : Bool

  bishopExpClassicalSemanticWeldOwned : Bool
  bishopSinClassicalSemanticWeldOwned : Bool
  bishopCosClassicalSemanticWeldOwned : Bool
  bishopPiClassicalSemanticWeldOwned : Bool
  actualAgdaVendorMirrorPackageInhabited : Bool

def vendoredTranscendentalExtractionBoundary :
    VendoredTranscendentalExtractionBoundary where
  vendoredArithmeticEvaluationOwned := true
  routeBPrimitiveExtractionCompilerOwned := true
  routeBComplexExtractionCompilerOwned := true

  bishopExpClassicalSemanticWeldOwned := false
  bishopSinClassicalSemanticWeldOwned := false
  bishopCosClassicalSemanticWeldOwned := false
  bishopPiClassicalSemanticWeldOwned := false
  actualAgdaVendorMirrorPackageInhabited := false

end

end Integration.BishopVendoredTranscendentalExtraction
