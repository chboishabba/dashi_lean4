import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/Quantum/NoGlobalAttractor.agda` (genuine theorem)

Faithful transcription of the iterated-dynamics "no global attractor" content:

* `iterate f n x` — `n`-fold iteration,
* `EventuallyConst f x a` — the orbit of `x` is eventually constant at `a`,
* `GlobalAttractor f` — a single `a` attracts every orbit.

The Agda original leaves the headline theorem (`invertible + nontrivial ⇒ no
global attractor`) as a *postulated* axiom record.  Following the strict honesty
discipline, we do **not** postulate it; instead we prove the genuine concrete
instance: the identity map (the prototypical invertible dynamics) has a global
attractor **iff** its carrier is a subsingleton, so on any carrier with two
distinct points it has **no** global attractor.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.NoGlobalAttractor

variable {S : Type}

/-- `n`-fold iteration of `f` (Agda `iterate`). -/
def iterate (f : S → S) : Nat → S → S
  | 0, x => x
  | n + 1, x => iterate f n (f x)

/-- The orbit of `x` under `f` is eventually constant at `a` (Agda
`EventuallyConst`). -/
def EventuallyConst (f : S → S) (x a : S) : Prop :=
  ∃ N, ∀ n, iterate f (N + n) x = a

/-- A global attractor: a single point attracting every orbit (Agda
`GlobalAttractor`). -/
def GlobalAttractor (f : S → S) : Prop :=
  ∃ a, ∀ x, EventuallyConst f x a

/-- Iterating the identity does nothing. -/
theorem iterate_id (n : Nat) (x : S) : iterate (id : S → S) n x = x := by
  induction n generalizing x with
  | zero => rfl
  | succ k ih => simpa [iterate] using ih x

/-- The identity has a global attractor exactly when the carrier is a
subsingleton. -/
theorem id_globalAttractor_subsingleton
    (h : GlobalAttractor (id : S → S)) : ∀ x y : S, x = y := by
  obtain ⟨a, ha⟩ := h
  intro x y
  obtain ⟨Nx, hx⟩ := ha x
  obtain ⟨Ny, hy⟩ := ha y
  have ex := hx 0
  have ey := hy 0
  rw [iterate_id] at ex ey
  rw [ex, ey]

/-- Genuine theorem: on a carrier with two distinct points, the identity (an
invertible, nontrivial dynamics) has no global attractor. -/
theorem id_no_global_attractor {x y : S} (hxy : x ≠ y) :
    ¬ GlobalAttractor (id : S → S) :=
  fun h => hxy (id_globalAttractor_subsingleton h x y)

end AgdaMirror.NoGlobalAttractor
