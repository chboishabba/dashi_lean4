import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Quantum/SignatureDerivation.agda`
(genuine honesty boundary: the axiom bundle is unsatisfiable)

Faithful transcription of the causal-signature derivation axiom bundle:

* `CausalCounts` — a pair `(tau, sigma)` of natural-number causal counts,
* `SignatureDerivationAxioms` — a measure `F : CausalCounts → Nat` required to be
  *homogeneous of degree two* (`F x = (l*l)·F x` for **all** `l`) and
  *cone-monotone* (`tau > sigma ⇒ F x > 0`).

These two requirements are jointly **contradictory over `ℕ`**: homogeneity at
`l = 0` forces `F ≡ 0`, but cone-monotonicity demands `F (1,0) > 0`.  Following
the strict honesty discipline (postulates/assumed bundles are never smuggled in
as axioms), we record this as a genuine *disproof*: no `SignatureDerivationAxioms`
can exist.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.SignatureDerivation

/-- A pair of causal counts (Agda `record CausalCounts`). -/
structure CausalCounts where
  tau : Nat
  sigma : Nat

/-- The causal-signature derivation axiom bundle (Agda
`record SignatureDerivationAxioms`); only the two genuinely constraining laws are
needed for the disproof. -/
structure SignatureDerivationAxioms where
  a : Nat
  b : Nat
  F : CausalCounts → Nat
  homogeneous : ∀ (l : Nat) (x : CausalCounts), F x = (l * l) * F x
  coneMonotone : ∀ (x : CausalCounts), x.tau > x.sigma → F x > 0

/-- Genuine disproof: the axiom bundle is unsatisfiable over `ℕ`. Homogeneity at
`l = 0` makes `F` vanish, contradicting cone-monotonicity at `(1,0)`. -/
theorem no_signature_derivation : SignatureDerivationAxioms → False := by
  intro D
  have hzero : D.F ⟨1, 0⟩ = 0 := by
    have := D.homogeneous 0 ⟨1, 0⟩
    simpa using this
  have hpos : D.F ⟨1, 0⟩ > 0 := D.coneMonotone ⟨1, 0⟩ (by decide)
  omega

end AgdaMirror.SignatureDerivation
