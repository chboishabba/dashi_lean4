import Welds.PNPOriginalResidualClosedInternalNoGoExact

/-!
Section38 — TIME-BOUNDED original external-observation witness.

Section37 established that a visible original anchored F3 residual
requires some non-closed observation, but the witness time was
unbounded and could occur AFTER the terminal consumer was evaluated.

Here the actual original deterministic finite transition is used
directly. For the two original legally reopened Boolean sources,
a fidelity-preserving terminal divergence at time k requires an
external-observation mismatch on one of those same two executions
at some j<k. No new observer, alternate F3 residual, oracle,
or machine resource is assumed. This is a temporal necessity,
not a quantitative lower bound on unrestricted SAT complexity.

Source-written pending native Lean and original dependency audit.
-/
namespace PNPOriginalResidualClosedEventNoGo
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary

theorem anchored_original_visible_external_observation_before_terminal
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (readout : Nat → S → I)
    (accept : S → Bool)
    (terminal : Syndrome m → Bool)
    (x : Fin n → Bool) (d : Syndrome n) (k : Nat)
    (hlegal : LegalAt x d)
    (hkernel : A d = 0)
    (hinit : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) →
      state u 0 = state v 0)
    (hstep : ∀ u j,
      state u (j+1) = step j (state u j) (observe j u))
    (hterminal : ∀ u,
      accept (state u k) = terminal (B (boolEmbed u)))
    (hvisible : terminal (B (boolEmbed x)) ≠
      terminal (B (boolEmbed (reopen x d)))) :
    ∃ j : Nat, j < k ∧
      (observe j x ≠ readout j (state x j) ∨
       observe j (reopen x d) ≠
         readout j (state (reopen x d) j)) := by
  classical
  let y := reopen x d
  have hdiff : boolEmbed x - boolEmbed y = d :=
    anchored_reopen x d hlegal
  have hretained : A (boolEmbed x) = A (boolEmbed y) := by
    apply sub_eq_zero.mp
    rw [← map_sub, hdiff, hkernel]
  have hinitial : state x 0 = state y 0 :=
    hinit x y hretained
  by_contra hn
  have hclosed (j : Nat) (hj : j < k) :
      observe j x = readout j (state x j) ∧
        observe j y = readout j (state y j) := by
    constructor
    · by_contra hx
      exact hn ⟨j, hj, Or.inl hx⟩
    · by_contra hy
      exact hn ⟨j, hj, Or.inr hy⟩
  have hequal : ∀ j, j ≤ k → state x j = state y j := by
    intro j
    induction j with
    | zero =>
        intro _
        exact hinitial
    | succ j ih =>
        intro hj
        have hlt : j < k := Nat.lt_of_succ_le hj
        have hp := hclosed j hlt
        rw [hstep x j, hstep y j, hp.1, hp.2, ih (Nat.le_of_lt hlt)]
  have hterminalEq := congrArg accept (hequal k (Nat.le_refl k))
  apply hvisible
  exact (hterminal x).symm.trans
    (hterminalEq.trans (hterminal y))

end PNPOriginalResidualClosedEventNoGo
