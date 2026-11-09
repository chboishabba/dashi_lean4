import Integration.JMD.CertifiedWorld

/-!
# Bidirectional round-trip stability

This is a *conditional* mathematical owner: both translators must provide
maps and their inverse laws. A syntactic conversion is not assumed to satisfy
these hypotheses. Theorems here express the exact necessary acceptance law,
not a claim that either real compiler has discharged it.
-/

namespace Integration.JMD.RoundTrip

/-- Evidence needed to transport a mathematical object without semantic drift. -/
structure CertifiedRoundTrip (A B : Type u) where
  toB : A → B
  toA : B → A
  leftInverse : ∀ a : A, toA (toB a) = a
  rightInverse : ∀ b : B, toB (toA b) = b

def toEquiv (r : CertifiedRoundTrip A B) : A ≃ B :=
  { toFun := r.toB
    invFun := r.toA
    left_inv := r.leftInverse
    right_inv := r.rightInverse }

theorem lean_agda_lean_stable (r : CertifiedRoundTrip A B)
    (a : A) : r.toA (r.toB a) = a :=
  r.leftInverse a

theorem agda_lean_agda_stable (r : CertifiedRoundTrip A B)
    (b : B) : r.toB (r.toA b) = b :=
  r.rightInverse b

theorem roundtrip_idempotent_left (r : CertifiedRoundTrip A B)
    (a : A) : r.toA (r.toB (r.toA (r.toB a))) = a := by
  rw [r.leftInverse, r.leftInverse]

theorem roundtrip_idempotent_right (r : CertifiedRoundTrip A B)
    (b : B) : r.toB (r.toA (r.toB (r.toA b))) = b := by
  rw [r.rightInverse, r.rightInverse]

/-- Predicate transport holds iff the source predicate holds. -/
def transportPredicate (r : CertifiedRoundTrip A B)
    (P : A → Prop) : B → Prop :=
  fun b => P (r.toA b)

theorem predicate_roundtrip (r : CertifiedRoundTrip A B)
    (P : A → Prop) (a : A) :
    transportPredicate r P (r.toB a) ↔ P a := by
  simp only [transportPredicate, r.leftInverse]

/-- A computational observer is preserved on return, not merely typechecked. -/
theorem observer_roundtrip (r : CertifiedRoundTrip A B)
    (observe : A → C) (a : A) :
    observe (r.toA (r.toB a)) = observe a := by
  rw [r.leftInverse]

/-- Inverse structure can be composed through an intermediate representation. -/
def trans (ab : CertifiedRoundTrip A B)
    (bc : CertifiedRoundTrip B C) : CertifiedRoundTrip A C where
  toB := bc.toB ∘ ab.toB
  toA := ab.toA ∘ bc.toA
  leftInverse := by
    intro a
    simp only [Function.comp_apply, bc.leftInverse, ab.leftInverse]
  rightInverse := by
    intro c
    simp only [Function.comp_apply, ab.rightInverse, bc.rightInverse]

theorem trans_source_stable (ab : CertifiedRoundTrip A B)
    (bc : CertifiedRoundTrip B C) (a : A) :
    (trans ab bc).toA ((trans ab bc).toB a) = a :=
  (trans ab bc).leftInverse a

end Integration.JMD.RoundTrip
