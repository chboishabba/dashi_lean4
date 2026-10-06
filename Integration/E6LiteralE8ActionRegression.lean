import Integration.E6LiteralE8Action

namespace Integration.E6LiteralE8ActionRegression

open Integration.E6LiteralE8Action

example : ∀ s root,
    vectorDot (embeddedE6Vector root) (simpleVector s) = 4 * cartanPairInt s root :=
  embedded_dot_simple_is_four_cartan_pair
example : ∀ s root, ∃! target : LiteralE6Sector,
    ∀ k, e8Coord target.1 k = reflectedEmbeddedVector s root k :=
  literal_reflection_unique_target
example : ∀ s root,
    standardAfterReflection s root =
      reflectStandard s (standardBeforeReflection root) :=
  mod3_standard_reflection_agrees
example : canonicalBoundary.literalE8ReflectionClosurePaid = true := rfl
example : canonicalBoundary.reflectionAndMod3ActionSynchronizedPaid = true := rfl
example : canonicalBoundary.actionDefinedByTransportOnly = false := rfl

end Integration.E6LiteralE8ActionRegression
