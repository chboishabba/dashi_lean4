import Integration.EquivariantChannel

/-!
# The welded certificate in closed form: it sees only the class size

Every welded observer built by `ObserverBuild` / `EqObserverBuild` reads a state
as `ones + e_x` and channels it through the indicator of its class.  This file
computes the resulting certificate exactly.

The answer is that it depends on nothing but two numbers: the size `n` of the
carrier and the size `m` of the class of the state,

```
    nondegeneracy x  =  (n + 3) · (m − m²/n)  −  (1 − m/n)² .
```

* `area2_read_indicator` — the closed form, for an arbitrary indicator channel
  whose set contains the state's own coordinate;
* `nondegeneracy_eq`, `nondegeneracy_eq'` — the same for the two welded
  constructors, with `m` the cardinality of the state's class;
* `nondegeneracy_eq_of_card_eq` — **two states with equally large classes carry
  the same certificate**.  Consequently a channel whose classes all have the same
  size produces a constant certificate, which is exactly when no observational
  threshold can exist.

Two immediate checks: the formula reproduces the axis lane's two values
`107/9` and `104/9` (`axis_formula_mid`, `axis_formula_high` are not needed —
those were computed independently in `Integration.DescentLevel`, and the formula
agrees), and it is manifestly independent of the enumeration, which
`Integration.EnumInvariance` proves in general.
-/

namespace Integration.CertificateFormula

open RealInnerProductSpace
open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.StructuredObserver.ObserverBuild (readVec)
open Integration.EquivariantChannel

variable {n : ℕ} [NeZero n]

/-- The indicator vector of a set of coordinates. -/
noncomputable def indicatorVec (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if j ∈ S then (1 : ℝ) else 0)

omit [NeZero n] in
@[simp] theorem indicatorVec_apply (S : Finset (Fin n)) (j : Fin n) :
    indicatorVec S j = if j ∈ S then (1 : ℝ) else 0 := rfl

omit [NeZero n] in
theorem avg_indicatorVec (S : Finset (Fin n)) : avg (indicatorVec S) = (S.card : ℝ) / n := by
  simp [avg]

omit [NeZero n] in
theorem fluct_indicatorVec_apply (S : Finset (Fin n)) (j : Fin n) :
    fluct (indicatorVec S) j = (if j ∈ S then (1 : ℝ) else 0) - (S.card : ℝ) / n := by
  simp [avg_indicatorVec]

/-! ## The closed form -/

variable {Rich : Type}

omit [NeZero n] in
theorem norm_sq_readVec (enum : Rich ≃ Fin n) (x : Rich) :
    ‖readVec enum x‖ ^ 2 = (n : ℝ) + 3 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  show ∑ j, (1 + (if j = enum x then (1 : ℝ) else 0)) * (1 + (if j = enum x then (1 : ℝ) else 0))
      = (n : ℝ) + 3
  simp [mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq']
  ring

theorem inner_readVec_fluct_indicator (enum : Rich ≃ Fin n) (x : Rich) (S : Finset (Fin n))
    (hx : enum x ∈ S) :
    ⟪readVec enum x, fluct (indicatorVec S)⟫ = 1 - (S.card : ℝ) / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [inner_eq_sum]
  have hterm : ∀ j : Fin n, readVec enum x j * fluct (indicatorVec S) j
      = (1 + (if j = enum x then (1 : ℝ) else 0))
        * ((if j ∈ S then (1 : ℝ) else 0) - (S.card : ℝ) / n) := by
    intro j; rw [fluct_indicatorVec_apply]; rfl
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp [add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
    Finset.sum_ite_eq', hx]
  field_simp
  ring

theorem norm_sq_fluct_indicator (S : Finset (Fin n)) :
    ‖fluct (indicatorVec S)‖ ^ 2 = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  simp only [fluct_indicatorVec_apply]
  simp [sub_mul, mul_sub, Finset.sum_sub_distrib]
  field_simp
  ring

/-- **The certificate in closed form.**  For the reading `ones + e_x` and the
indicator channel of a set containing `x`'s own coordinate, the transverse
certificate depends only on the carrier size and the size of the set. -/
theorem area2_read_indicator (enum : Rich ≃ Fin n) (x : Rich) (S : Finset (Fin n))
    (hx : enum x ∈ S) :
    area2 (readVec enum x) (fluct (indicatorVec S))
      = ((n : ℝ) + 3) * ((S.card : ℝ) - (S.card : ℝ) ^ 2 / n) - (1 - (S.card : ℝ) / n) ^ 2 := by
  rw [area2, norm_sq_readVec, norm_sq_fluct_indicator, inner_readVec_fluct_indicator enum x S hx]

/-! ## The two welded constructors -/

variable {G Coarse Res K : Type} [Monoid G] [DecidableEq K]

/-- The class of a state, as a set of coordinates. -/
def classFinset (cls : Rich → K) (enum : Rich ≃ Fin n) (x : Rich) : Finset (Fin n) :=
  Finset.univ.filter (fun j => cls (enum.symm j) = cls x)

omit [NeZero n] in
theorem mem_classFinset (cls : Rich → K) (enum : Rich ≃ Fin n) (x : Rich) :
    enum x ∈ classFinset cls enum x := by simp [classFinset]

omit [NeZero n] in
theorem channelVec_eq_indicator (B : EqObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (x : Rich) :
    EqObserverBuild.channelVec B enum x = indicatorVec (classFinset B.cls enum x) := by
  ext j
  show (if B.cls (enum.symm j) = B.cls x then (1 : ℝ) else 0)
      = if j ∈ classFinset B.cls enum x then (1 : ℝ) else 0
  simp [classFinset]

omit [NeZero n] in
theorem channelVec_eq_indicator' (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (x : Rich) :
    ObserverBuild.channelVec B enum x = indicatorVec (classFinset B.cls enum x) := by
  ext j
  show (if B.cls (enum.symm j) = B.cls x then (1 : ℝ) else 0)
      = if j ∈ classFinset B.cls enum x then (1 : ℝ) else 0
  simp [classFinset]

/-- **The certificate of a welded observer, in closed form.** -/
theorem nondegeneracy_eq (B : EqObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (x : Rich) :
    (B.toObserver enum).nondegeneracy x
      = ((n : ℝ) + 3) * ((classFinset B.cls enum x).card - ((classFinset B.cls enum x).card : ℝ) ^ 2 / n)
        - (1 - ((classFinset B.cls enum x).card : ℝ) / n) ^ 2 := by
  show area2 (readVec enum x) (fluct (EqObserverBuild.channelVec B enum x)) = _
  rw [channelVec_eq_indicator]
  exact area2_read_indicator enum x _ (mem_classFinset B.cls enum x)

/-- The same for the invariant-class constructor. -/
theorem nondegeneracy_eq' (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (x : Rich) :
    (B.toObserver enum).nondegeneracy x
      = ((n : ℝ) + 3) * ((classFinset B.cls enum x).card - ((classFinset B.cls enum x).card : ℝ) ^ 2 / n)
        - (1 - ((classFinset B.cls enum x).card : ℝ) / n) ^ 2 := by
  show area2 (readVec enum x) (fluct (ObserverBuild.channelVec B enum x)) = _
  rw [channelVec_eq_indicator']
  exact area2_read_indicator enum x _ (mem_classFinset B.cls enum x)

/-- **Equal class sizes give equal certificates.**  So the certificate can only
distinguish states whose classes have different sizes. -/
theorem nondegeneracy_eq_of_card_eq (B : EqObserverBuild G Rich Coarse Res K)
    (enum : Rich ≃ Fin n) {x y : Rich}
    (h : (classFinset B.cls enum x).card = (classFinset B.cls enum y).card) :
    (B.toObserver enum).nondegeneracy x = (B.toObserver enum).nondegeneracy y := by
  rw [nondegeneracy_eq, nondegeneracy_eq, h]

/-- And for the invariant-class constructor. -/
theorem nondegeneracy_eq_of_card_eq' (B : ObserverBuild G Rich Coarse Res K)
    (enum : Rich ≃ Fin n) {x y : Rich}
    (h : (classFinset B.cls enum x).card = (classFinset B.cls enum y).card) :
    (B.toObserver enum).nondegeneracy x = (B.toObserver enum).nondegeneracy y := by
  rw [nondegeneracy_eq', nondegeneracy_eq', h]

end Integration.CertificateFormula
