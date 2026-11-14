import Integration.E6Mod3ReflectionIntertwiner

namespace Integration.E6Mod3ReflectionIntertwinerRegression

open Integration.E6Mod3ReflectionIntertwiner

example : ∀ s x, e6Mod3Quadratic (reflectF3Six s x) = e6Mod3Quadratic x :=
  reflection_preserves_cartan_quadratic
example : ∀ s a x,
    reflectF3Six s (radicalTranslate a x) = radicalTranslate a (reflectF3Six s x) :=
  reflection_commutes_radical_translation
example : ∀ s x,
    quotientToStandard (quotientCoordinates (reflectF3Six s x)) =
      reflectStandard s (quotientToStandard (quotientCoordinates x)) :=
  quotient_isometry_intertwines_reflection
example : canonicalBoundary.globalIntertwiningAll729Paid = true := rfl
example : canonicalBoundary.oldPartialIntertwiningInterpretationRetained = false := rfl

end Integration.E6Mod3ReflectionIntertwinerRegression
