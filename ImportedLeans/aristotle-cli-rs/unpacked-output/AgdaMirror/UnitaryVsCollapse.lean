import AgdaMirror.Scaffolding

/-!
# Lean mirror of `DASHI/Algebra/UnitaryVsCollapse.agda` (genuine theorem)

Faithful transcription of the genuine dynamical fact: in an inhabited system with
an invertible step and a `ℕ`-valued energy `H`, "strict collapse everywhere"
(every step strictly decreases `H`) is impossible — there is no infinite descent
in `ℕ`.

* `InvertibleNat` — a step system with a two-sided inverse and `ℕ`-energy;
* `iterate` — iterated application of the step;
* `no_global_strict_collapse` — the impossibility result, proved from the
  no-infinite-descent lemma (`AgdaMirror.Scaffolding.no_infinite_descent`).

No `sorry`, axiom-clean.
-/

namespace AgdaMirror.UnitaryVsCollapse

/-- A step system with a two-sided inverse and a `ℕ`-valued energy. -/
structure InvertibleNat (S : Type) where
  step : S → S
  inv : S → S
  left : ∀ s, inv (step s) = s
  right : ∀ s, step (inv s) = s
  H : S → Nat

/-- Iterated application of a self-map. -/
def iterate {S : Type} (f : S → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- In an inhabited system, strict energy collapse on every step is impossible
(mirrors `no-global-strict-collapse`). -/
theorem no_global_strict_collapse {S : Type} (U : InvertibleNat S) (s0 : S) :
    ¬ (∀ s, U.H (U.step s) < U.H s) := by
  intro strict
  exact AgdaMirror.Scaffolding.no_infinite_descent U.H U.step strict s0

end AgdaMirror.UnitaryVsCollapse
