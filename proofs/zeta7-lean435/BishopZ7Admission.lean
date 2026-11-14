import ZetaIrrational.Z7.MainUnconditional
import Mathlib.Tactic

/-!
# Pinned external Z7 odd-zeta theorem admission (Lean 4.35 sidecar)

EXTERNAL MATHEMATICAL AND FORMAL SOURCE
  Shawn Krisman, telaviv/zeta-irrationality tag v1.0,
  using Zudilin (2004) and the Ball–Rivoal/Rivoal lineage.
  External theorem: ZetaIrr.Z7.oneOfZeta7To21.
  Its proof, numerical certificates, and authorship belong to that repo.

DASHI CONTRIBUTION
  * exact external finite-set -> Fin 8 witness transport;
  * inject into the 15-value window {5,7,...,33};
  * turn real-part irrationality into complex-rational exclusion;
  * transfer that witness along an EXPLICIT same-value equality.

The original dashi_lean4 Mathlib pin differs from this sidecar's
v4.35.0 package; a cross-version binary/olean theorem import is
not asserted. Nothing here identifies an Agda Bishop-real value
without an independently proved semantic correspondence.
No index is numerically selected from the existential proof.

Source-written; the local Lake build and axiom audit are required
for admission, not assumed to have run.
-/

namespace BishopZ7Admission

noncomputable section

def intoFifteen (k : Fin 8) : Fin 15 :=
  ⟨k.val + 1, by omega⟩

theorem intoFifteenArgument (k : Fin 8) :
    5 + 2 * (intoFifteen k).val = 7 + 2 * k.val := by
  simp [intoFifteen]
  omega

/-- Exact Finset membership of the EXTERNAL theorem, not a
substitute or newly asserted irrationality statement. -/
theorem z7WitnessFin8 :
    ∃ k : Fin 8,
      Irrational (riemannZeta ((7 + 2 * k.val : ℕ) : ℂ)).re := by
  obtain ⟨j, hj, hirr⟩ := ZetaIrr.Z7.oneOfZeta7To21
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h7 | h9 | h11 | h13 | h15 | h17 | h19 | h21
  · subst j
    exact ⟨⟨0, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨1, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨2, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨3, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨4, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨5, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨6, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨7, by decide⟩, by simpa using hirr⟩

theorem z7WitnessFin15 :
    ∃ k : Fin 15,
      Irrational (riemannZeta ((5 + 2 * k.val : ℕ) : ℂ)).re := by
  obtain ⟨k, hirr⟩ := z7WitnessFin8
  refine ⟨intoFifteen k, ?_⟩
  simpa only [intoFifteenArgument k] using hirr

/-- The external theorem's real-part irrationality implies
the genuine complex value is NOT a rational-number cast.
No realness hypothesis is required for this direction. -/
theorem z7WitnessComplexNotRational :
    ∃ k : Fin 15,
      ¬ ∃ q : ℚ, riemannZeta ((5 + 2 * k.val : ℕ) : ℂ) = (q : ℂ) := by
  obtain ⟨k, hirr⟩ := z7WitnessFin15
  refine ⟨k, ?_⟩
  rintro ⟨q, hq⟩
  apply hirr
  refine ⟨q, ?_⟩
  simpa using congrArg Complex.re hq.symm

/-- Exact same-value transport: the user must supply a proof that
their selected source carrier evaluates to THIS actual Mathlib zeta
at every requested integer. This is NOT an imported Agda proof. -/
theorem z7WitnessForSource
    (sourceValue : Fin 15 → ℂ)
    (sameValue : ∀ k : Fin 15,
      sourceValue k = riemannZeta ((5 + 2 * k.val : ℕ) : ℂ)) :
    ∃ k : Fin 15, ¬ ∃ q : ℚ, sourceValue k = (q : ℂ) := by
  obtain ⟨k, hnot⟩ := z7WitnessComplexNotRational
  refine ⟨k, ?_⟩
  rintro ⟨q, hq⟩
  exact hnot ⟨q, (sameValue k).symm.trans hq⟩

#print axioms ZetaIrr.Z7.oneOfZeta7To21
#print axioms z7WitnessFin8
#print axioms z7WitnessComplexNotRational
#print axioms z7WitnessForSource

end
end BishopZ7Admission
