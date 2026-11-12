import Integration.PositiveOddZetaImaginaryZeroExact
import Integration.BishopOddZetaNarrowWindowTransport
import Mathlib.Tactic

/-!
# Z7 finite-set witness -> original Bishop Dirichlet value

External theorem SOURCE:
  Shawn Krisman, telaviv/zeta-irrationality,
  ZetaIrrational/Statement.lean and Z7/MainUnconditional.lean.
  ZetaIrr.Z7.oneOfZeta7To21 is the external theorem and its
  exact statement is mirrored below in `Z7StatementShape`.
  Its proof term is NOT imported into this v4.28 Mathlib dependency.
  The source repository has a different Lean/Mathlib pin.

DASHI CONTRIBUTION:
  * literal eight-set membership -> Fin 8 index;
  * equality-preserving embedding into original Fin 15 Bishop window;
  * eliminate the former free zeta-real-valuedness hypothesis by
    the explicit Dirichlet/Mathlib theorem;
  * package the exact conditional consequence of the external theorem.
No numerical witness is invented by the existential elimination.
-/

namespace Integration.BishopOddZetaZ7FinsetBridgeExact

open Integration.BishopOddZetaHalfPlaneSpecialization
open Integration.BishopOddZetaNarrowWindowTransport
open Integration.PositiveOddZetaImaginaryZeroExact
open Integration.BishopRiemannZetaNativeMachinContinuity

noncomputable section

/-- Signature-only mirror of the external declaration; NOT its proof. -/
def Z7StatementShape : Prop :=
  ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ),
    Irrational (riemannZeta (j : ℂ)).re

theorem z7FinsetWitness_to_fin8 (h : Z7StatementShape) :
    ∃ k : Fin 8,
      Irrational (riemannZeta ((7 + 2 * k.val : ℕ) : ℂ)).re := by
  obtain ⟨j, hj, hirr⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h7 | h9 | h11 | h13 | h15 | h17 | h19 | h21
  · subst j
    exact ⟨⟨0, by decide⟩, by simpa using hirr⟩
  · subst j
    exact ⟨⟨1, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩
  · subst j
    exact ⟨⟨2, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩
  · subst j
    exact ⟨⟨3, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩
  · subst j
    exact ⟨⟨4, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩
  · subst j
    exact ⟨⟨5, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩
  · subst j
    exact ⟨⟨6, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩
  · subst j
    exact ⟨⟨7, by decide⟩, by simpa only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd] using hirr⟩

/-- Remove the free imaginary-part hypothesis from the previous
transport, by a separate actual Mathlib zeta theorem. -/
theorem z7FinsetWitness_to_originalDirichlet
    (h : Z7StatementShape) :
    ∃ k : Fin 15,
      ¬ HasRationalComplexValue
        (originalDirichletValue ((oddArgument k.val : ℕ) : ℂ)) :=
  narrowerWitness_to_originalSource
    z7_eight_window_im_zero
    (z7FinsetWitness_to_fin8 h)

/-- Map an externally established disjunction into the genuine zeta
15-window, preserving the selected integer. -/
theorem z7FinsetWitness_to_genuineZeta15
    (h : Z7StatementShape) :
    ∃ k : Fin 15,
      ¬ HasRationalComplexValue
        (riemannZeta ((oddArgument k.val : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := z7FinsetWitness_to_originalDirichlet h
  refine ⟨k, ?_⟩
  rwa [originalOddWindow_eq_riemannZeta] at hk

#print axioms z7FinsetWitness_to_fin8
#print axioms z7FinsetWitness_to_originalDirichlet

end
end Integration.BishopOddZetaZ7FinsetBridgeExact
