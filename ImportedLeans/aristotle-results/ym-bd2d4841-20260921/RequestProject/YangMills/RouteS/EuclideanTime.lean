/-
# `S₂`: Euclidean time on the literal lattice, and what "separation `t`" means

Route `S` insists that the separation appearing in the source/clustering
estimate is *physical Euclidean separation* in the reconstructed time
direction, not a formal coordinate attached to a source label.  On the literal
periodic lattice of `Lattice/Wilson.lean` this is a statement one can simply
prove, and this file proves it:

* `timeVec`, `timeTranslate` — the lattice vector of `t` steps in the
  distinguished (time) direction and the corresponding translation of
  configurations;
* `timeTranslate_zero`, `timeTranslate_add` — the time translations form an
  action of the additive monoid `ℕ` (`τ_s ∘ τ_t = τ_{s+t}`), so "separation
  `t`" is `t` applications of the one-step translation and nothing else;
* `measurePreserving_timeTranslate_gibbs` — the literal Wilson–Gibbs measure is
  invariant under Euclidean time translations;
* `wilsonLoop_timeTranslate` — the time translate of a literal Wilson-loop
  observable is the literal Wilson-loop observable of the loop moved `t` steps
  in the time direction.  This is the content of `S₂`: the "distance"
  coordinate in `Cov(A, τ_t B)` is the displacement of the support of the
  observable along the Euclidean time axis.
-/
import Mathlib
import RequestProject.YangMills.Lattice.WilsonLoop

namespace RequestProject.YangMills.RouteS

open RequestProject.YangMills.Lattice
open MeasureTheory

/-- The distinguished Euclidean time direction of the four-dimensional
lattice. -/
def timeDir : Fin 4 := 0

variable {n : ℕ}

/-- The lattice vector of `t` steps in the Euclidean time direction. -/
def timeVec (n : ℕ) (t : ℕ) : Site n := Pi.single timeDir (t : ZMod (n + 1))

@[simp] theorem timeVec_zero : timeVec n 0 = 0 := by
  simp [timeVec]

theorem timeVec_add (s t : ℕ) : timeVec n (s + t) = timeVec n s + timeVec n t := by
  simp [timeVec, Nat.cast_add, Pi.single_add]

theorem timeVec_succ (t : ℕ) : timeVec n (t + 1) = timeVec n t + timeVec n 1 := by
  rw [timeVec_add]

section Action

variable {G : Type*} [Group G]

/-- Euclidean time translation of a configuration by `t` lattice steps. -/
def timeTranslate (n : ℕ) (t : ℕ) (U : Conf n G) : Conf n G :=
  translate (timeVec n t) U

omit [Group G] in
@[simp] theorem timeTranslate_zero (U : Conf n G) : timeTranslate n 0 U = U := by
  funext l
  show U (l.1 + timeVec n 0, l.2) = U l
  rw [timeVec_zero, add_zero]

omit [Group G] in
/-- Euclidean time translations compose: `τ_s ∘ τ_t = τ_{s+t}`. -/
theorem timeTranslate_add (s t : ℕ) (U : Conf n G) :
    timeTranslate n s (timeTranslate n t U) = timeTranslate n (s + t) U := by
  funext l
  show U (l.1 + timeVec n s + timeVec n t, l.2) = U (l.1 + timeVec n (s + t), l.2)
  rw [timeVec_add, add_assoc]

omit [Group G] in
/-- Hence `τ_t` is the `t`-fold iterate of the one-step time translation:
the separation coordinate really counts lattice time steps. -/
theorem timeTranslate_eq_iterate (t : ℕ) (U : Conf n G) :
    timeTranslate n t U = (timeTranslate n 1)^[t] U := by
  induction t generalizing U with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply, ← ih, timeTranslate_add]

end Action

section Literal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- The literal Wilson–Gibbs measure is invariant under Euclidean time
translations. -/
theorem measurePreserving_timeTranslate_gibbs {chi : G → ℝ} (hchi : Continuous chi)
    (beta : ℝ) (t : ℕ) :
    MeasurePreserving (timeTranslate (G := G) n t) (gibbs n G beta chi) (gibbs n G beta chi) :=
  measurePreserving_translate_gibbs hchi beta _

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **`S₂` on the literal lattice.**  Composing a literal Wilson-loop observable
with the Euclidean time translation by `t` gives exactly the Wilson-loop
observable of the same loop moved `t` steps along the time axis: the separation
coordinate is physical Euclidean separation. -/
theorem wilsonLoop_timeTranslate (chi : G → ℝ) (x : Site n) (p : List Step) (t : ℕ)
    (U : Conf n G) :
    wilsonLoop chi x p (timeTranslate n t U) = wilsonLoop chi (x + timeVec n t) p U :=
  wilsonLoop_translate chi x _ p U

end Literal

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms timeTranslate_add
#print axioms timeTranslate_eq_iterate
#print axioms measurePreserving_timeTranslate_gibbs
#print axioms wilsonLoop_timeTranslate

end Audit
