import Integration.ObserverDescent
import Integration.PhysicsInstances
import Integration.GaugeSU2

/-!
# How coarse an observer may be before an invariant stops being visible

`Integration.ObserverDescent` answers "does this certificate descend one level?".
The corpus-wide question is sharper: given a whole tower of observers

```
X₀ ──▶ X₁ ──▶ X₂ ──▶ ⋯
```

(each arrow a further coarsening) and an invariant `c : X₀ → ℝ`, at which levels
is `c` still a function of the observed state?  Since factoring through level
`k+1` implies factoring through level `k`, the set of sufficient levels is an
initial segment, and the meaningful datum is its **last** element: the coarsest
observation at which the invariant is still visible.  That is the *minimum
observational resolution required to retain the invariant*.

* `LayerTower` — a sequence of carriers with a coarsening between consecutive
  levels; `projTo` is the composite from the finest level.
* `FactorsAt T c k` — `c` is a function of the level-`k` observation.
* `factorsAt_zero`, `factorsAt_of_le` — always true at the finest level, and
  downward closed, so the sufficient levels form an initial segment.
* `factorsAt_iff_fibre` — the exact criterion: `c` factors at level `k` iff it is
  constant on the fibres of `projTo k`.
* `CoarsestSufficient T c k` — factors at `k`, fails at `k+1`.
  `coarsest_unique` and `exists_coarsest` make it a well-defined number whenever
  the invariant fails somewhere up the tower.
* `factorsAt_of_orbitFibred` — the bridge to the welded schema: an orbit-fibred
  symmetry-resolved observer's transverse certificate factors at its own visible
  level.

The concrete instance is the finite axis-lift lane.  With the transverse class
coordinate "is this the distinguished axis?", the certificate takes two distinct
values (`highObserver_cert`), so:

* it factors at the axis level (`cert_factorsAt_one`, via orbit-fibredness);
* it does not factor at the next coarsening, which merges the distinguished axis
  with another one (`cert_not_factorsAt_two`);

hence `axis_coarsest_sufficient`: the coarsest sufficient observer for this
certificate is exactly the three-axis layer.
-/

namespace Integration.DescentLevel

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.StructuredObserver.ObserverBuild
open Integration.ObserverDescent
open Integration.SSPWeave
open Integration.Physics369
open Integration.GaugeSU2

/-! ## Towers of observers -/

/-- A tower of successively coarser carriers. -/
structure LayerTower where
  /-- The carrier at each level; level `0` is the finest. -/
  Layer : ℕ → Type
  /-- The coarsening from one level to the next. -/
  step : ∀ k, Layer k → Layer (k + 1)

namespace LayerTower

/-- The composite observation map from the finest level to level `k`. -/
def projTo (T : LayerTower) : (k : ℕ) → (T.Layer 0 → T.Layer k)
  | 0 => id
  | k + 1 => fun x => T.step k (projTo T k x)

@[simp] theorem projTo_zero (T : LayerTower) (x : T.Layer 0) : T.projTo 0 x = x := rfl

@[simp] theorem projTo_succ (T : LayerTower) (k : ℕ) (x : T.Layer 0) :
    T.projTo (k + 1) x = T.step k (T.projTo k x) := rfl

/-- An invariant of the finest level **factors at level `k`** if it is a function
of the level-`k` observation. -/
def FactorsAt (T : LayerTower) (c : T.Layer 0 → ℝ) (k : ℕ) : Prop :=
  ∃ f : T.Layer k → ℝ, ∀ x, c x = f (T.projTo k x)

/-- Every invariant is visible at the finest level. -/
theorem factorsAt_zero (T : LayerTower) (c : T.Layer 0 → ℝ) : T.FactorsAt c 0 :=
  ⟨c, fun _ => rfl⟩

/-- Visibility is inherited by finer levels. -/
theorem factorsAt_of_succ (T : LayerTower) (c : T.Layer 0 → ℝ) {k : ℕ}
    (h : T.FactorsAt c (k + 1)) : T.FactorsAt c k := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun y => f (T.step k y), fun x => hf x⟩

/-- So the sufficient levels form an initial segment. -/
theorem factorsAt_of_le (T : LayerTower) (c : T.Layer 0 → ℝ) {k m : ℕ} (hkm : k ≤ m)
    (h : T.FactorsAt c m) : T.FactorsAt c k := by
  induction m with
  | zero => rw [Nat.le_zero.mp hkm]; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact ih (Nat.lt_succ_iff.mp hlt) (T.factorsAt_of_succ c h)
    · have : k = m + 1 := le_antisymm hkm hge
      subst this; exact h

/-- **The criterion.**  An invariant factors at a level exactly when it is
constant on the fibres of the observation at that level. -/
theorem factorsAt_iff_fibre (T : LayerTower) (c : T.Layer 0 → ℝ) (k : ℕ) :
    T.FactorsAt c k ↔ ∀ x y, T.projTo k x = T.projTo k y → c x = c y := by
  classical
  constructor
  · rintro ⟨f, hf⟩ x y hxy
    rw [hf x, hf y, hxy]
  · intro h
    refine ⟨fun z => if hz : ∃ x, T.projTo k x = z then c hz.choose else 0, fun x => ?_⟩
    have hex : ∃ x', T.projTo k x' = T.projTo k x := ⟨x, rfl⟩
    show c x = if hz : ∃ x', T.projTo k x' = T.projTo k x then c hz.choose else 0
    rw [dif_pos hex]
    exact (h _ _ hex.choose_spec).symm

/-- **The coarsest sufficient observation**: the invariant is still a function of
the level-`k` state, but not of the level-`(k+1)` state. -/
def CoarsestSufficient (T : LayerTower) (c : T.Layer 0 → ℝ) (k : ℕ) : Prop :=
  T.FactorsAt c k ∧ ¬ T.FactorsAt c (k + 1)

/-- It is unique when it exists, so "the minimum observational resolution
retaining the invariant" is a well-defined number. -/
theorem coarsest_unique (T : LayerTower) (c : T.Layer 0 → ℝ) {k m : ℕ}
    (hk : T.CoarsestSufficient c k) (hm : T.CoarsestSufficient c m) : k = m := by
  by_contra hne
  rcases Nat.lt_or_ge k m with hlt | hge
  · exact hk.2 (T.factorsAt_of_le c hlt hm.1)
  · have hlt : m < k := lt_of_le_of_ne hge (Ne.symm hne)
    exact hm.2 (T.factorsAt_of_le c hlt hk.1)

/-- And it exists as soon as the invariant is lost somewhere up the tower. -/
theorem exists_coarsest (T : LayerTower) (c : T.Layer 0 → ℝ)
    (hlost : ∃ N, ¬ T.FactorsAt c N) : ∃ k, T.CoarsestSufficient c k := by
  classical
  have hNspec : ¬ T.FactorsAt c (Nat.find hlost) := Nat.find_spec hlost
  have hNpos : Nat.find hlost ≠ 0 := by
    intro h0
    exact hNspec (by rw [h0]; exact T.factorsAt_zero c)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hlost = k + 1 := ⟨Nat.find hlost - 1, by omega⟩
  refine ⟨k, ?_, hk ▸ hNspec⟩
  by_contra hkf
  have hle : Nat.find hlost ≤ k := Nat.find_le hkf
  omega

/-- A constant invariant is visible at every level: nothing is lost by
coarsening, so no coarsest sufficient level exists. -/
theorem factorsAt_of_constant (T : LayerTower) (c : T.Layer 0 → ℝ) (r : ℝ)
    (hc : ∀ x, c x = r) (k : ℕ) : T.FactorsAt c k :=
  ⟨fun _ => r, fun x => hc x⟩

end LayerTower

/-! ## Towers from observers -/

open LayerTower

/-- The two-step tower `Rich → Mid → Coarse` (constant above level two). -/
def twoStepTower {Rich Mid Coarse : Type} (p : Rich → Mid) (q : Mid → Coarse) : LayerTower where
  Layer
    | 0 => Rich
    | 1 => Mid
    | 2 => Coarse
    | _ + 3 => PUnit
  step
    | 0 => p
    | 1 => q
    | 2 => fun _ => PUnit.unit
    | _ + 3 => fun _ => PUnit.unit

@[simp] theorem twoStepTower_projTo_one {Rich Mid Coarse : Type} (p : Rich → Mid)
    (q : Mid → Coarse) (x : Rich) : (twoStepTower p q).projTo 1 x = p x := rfl

@[simp] theorem twoStepTower_projTo_two {Rich Mid Coarse : Type} (p : Rich → Mid)
    (q : Mid → Coarse) (x : Rich) : (twoStepTower p q).projTo 2 x = q (p x) := rfl

/-- **The bridge to the welded schema.**  If a symmetry-resolved observer is
orbit-fibred then its transverse certificate factors at its own visible level of
the tower it heads. -/
theorem factorsAt_one_of_orbitFibred {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
    (O : SymmetryResolvedObserver G Rich Coarse Res n) (horb : OrbitFibred O)
    {C : Type} (q : Coarse → C) :
    (twoStepTower O.reduction.proj q).FactorsAt O.nondegeneracy 1 := by
  rw [LayerTower.factorsAt_iff_fibre]
  intro x y hxy
  obtain ⟨g, rfl⟩ := horb x y hxy
  exact (O.nondegeneracy_invariant g x).symm

/-- **A transitive symmetry flattens the certificate.**  If the symmetry acts
transitively on the rich carrier then the certificate is constant, hence visible
at *every* level: such a certificate carries no information about observational
resolution. -/
theorem factorsAt_all_of_transitive {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
    [Nonempty Rich] (O : SymmetryResolvedObserver G Rich Coarse Res n)
    (htrans : ∀ x y : Rich, ∃ g, y = O.reduction.actRich g x)
    {C : Type} (q : Coarse → C) (k : ℕ) :
    (twoStepTower O.reduction.proj q).FactorsAt O.nondegeneracy k := by
  obtain ⟨x₀⟩ := ‹Nonempty Rich›
  refine LayerTower.factorsAt_of_constant _ _ (O.nondegeneracy x₀) (fun x => ?_) k
  obtain ⟨g, rfl⟩ := htrans x₀ x
  exact O.nondegeneracy_invariant g x₀

/-! ## The concrete instance: at what resolution is the certificate still visible?

The finite axis-lift lane again, with the transverse class coordinate "is this
the distinguished axis?".  The two classes have different sizes, so the
certificate takes two different values, and the level at which it stops being
observable can be located exactly. -/

/-- Observer data on the axis-lift lane whose transverse class coordinate
separates the distinguished axis from the other two.  The classes then have
sizes four and two, so the certificate is not constant. -/
def highBuild : ObserverBuild FibreOrientation AxisLift SU2Axis LiftPolarity Bool where
  reduction := axisReduction
  actInv := liftAction
  actInv_left := liftAction_involutive
  actInv_right := liftAction_involutive
  residual := Prod.snd
  reopen := fun a p => (a, p)
  reopen_project := fun _ => rfl
  cls := fun x => decide (x.1 = SU2Axis.axisHigh)
  cls_invariant := by decide
  cls_separates := by decide

/-- The resulting symmetry-resolved observer. -/
noncomputable def highObserver :
    SymmetryResolvedObserver FibreOrientation AxisLift SU2Axis LiftPolarity 6 :=
  highBuild.toObserver axisEnum

/-- The certificate written out as coordinate sums, ready for evaluation. -/
theorem cert_eq_sums (x : AxisLift) :
    highObserver.nondegeneracy x
      = (∑ i, readVec axisEnum x i * readVec axisEnum x i)
          * (∑ i, fluct (channelVec highBuild axisEnum x) i
              * fluct (channelVec highBuild axisEnum x) i)
        - (∑ i, readVec axisEnum x i * fluct (channelVec highBuild axisEnum x) i) ^ 2 := by
  simp only [SymmetryResolvedObserver.nondegeneracy, highObserver, ObserverBuild.toObserver,
    Spine.area2, ← real_inner_self_eq_norm_sq, inner_eq_sum]

theorem chanMid : channelVec highBuild axisEnum (SU2Axis.axisMid, LiftPolarity.pos)
    = (WithLp.toLp 2 ![1, 1, 1, 1, 0, 0] : EuclideanSpace ℝ (Fin 6)) := by
  ext j; fin_cases j <;> simp [channelVec, highBuild, axisEnum]

theorem readMid : readVec axisEnum (SU2Axis.axisMid, LiftPolarity.pos)
    = (WithLp.toLp 2 ![1, 1, 2, 1, 1, 1] : EuclideanSpace ℝ (Fin 6)) := by
  ext j
  fin_cases j <;> simp [readVec, axisEnum, Fin.ext_iff]
  norm_num

theorem chanHigh : channelVec highBuild axisEnum (SU2Axis.axisHigh, LiftPolarity.pos)
    = (WithLp.toLp 2 ![0, 0, 0, 0, 1, 1] : EuclideanSpace ℝ (Fin 6)) := by
  ext j; fin_cases j <;> simp [channelVec, highBuild, axisEnum]

theorem readHigh : readVec axisEnum (SU2Axis.axisHigh, LiftPolarity.pos)
    = (WithLp.toLp 2 ![1, 1, 1, 1, 2, 1] : EuclideanSpace ℝ (Fin 6)) := by
  ext j
  fin_cases j <;> simp [readVec, axisEnum, Fin.ext_iff]
  norm_num

/-- The certificate on a state of the four-element class. -/
theorem cert_mid : highObserver.nondegeneracy (SU2Axis.axisMid, LiftPolarity.pos) = 107 / 9 := by
  rw [cert_eq_sums, chanMid, readMid]
  simp [avg, Fin.sum_univ_six]
  norm_num

/-- The certificate on a state of the two-element class: a different value, so
this certificate is a genuinely nonconstant invariant. -/
theorem cert_high : highObserver.nondegeneracy (SU2Axis.axisHigh, LiftPolarity.pos) = 104 / 9 := by
  rw [cert_eq_sums, chanHigh, readHigh]
  simp [avg, Fin.sum_univ_six]
  norm_num

/-- The lane is orbit-fibred: two lifts of the same axis differ by the central
flip. -/
theorem high_orbitFibred : OrbitFibred highObserver := by
  intro x y h
  have h' : x.1 = y.1 := h
  revert h'
  revert x y
  decide

/-- The level-two observation: it merges the distinguished axis with one of the
others, so it cannot see the class the certificate depends on. -/
def axisMerge : SU2Axis → Bool
  | .axisLow => true
  | .axisMid => false
  | .axisHigh => false

/-- The tower `6 cover points → 3 axes → 2 merged classes`. -/
def axisTower : LayerTower := twoStepTower (Prod.fst : AxisLift → SU2Axis) axisMerge

/-- The certificate is visible at the axis level. -/
theorem cert_factorsAt_one : axisTower.FactorsAt highObserver.nondegeneracy 1 :=
  factorsAt_one_of_orbitFibred highObserver high_orbitFibred axisMerge

/-- It is not visible at the next coarsening: two states with the same merged
label carry different certificates. -/
theorem cert_not_factorsAt_two : ¬ axisTower.FactorsAt highObserver.nondegeneracy 2 := by
  rw [LayerTower.factorsAt_iff_fibre]
  intro h
  have hval := h (SU2Axis.axisMid, LiftPolarity.pos) (SU2Axis.axisHigh, LiftPolarity.pos) rfl
  rw [cert_mid, cert_high] at hval
  norm_num at hval

/-- **The minimum observational resolution.**  The coarsest observation of this
lane at which the transverse certificate is still a function of the observed
state is the three-axis layer; one further coarsening loses it. -/
theorem axis_coarsest_sufficient : axisTower.CoarsestSufficient highObserver.nondegeneracy 1 :=
  ⟨cert_factorsAt_one, cert_not_factorsAt_two⟩

/-- And that level is the only one with this property. -/
theorem axis_coarsest_unique {k : ℕ}
    (hk : axisTower.CoarsestSufficient highObserver.nondegeneracy k) : k = 1 :=
  LayerTower.coarsest_unique _ _ hk axis_coarsest_sufficient

/-! ## The contrast: the gauge-reduced lane's certificate has no threshold

The same six cover points, but now under the enlarged symmetry `C₂ × C₃` of
`Integration.GaugeSU2`, which acts transitively.  Its certificate is therefore
constant and survives every coarsening — so no `CoarsestSufficient` level
exists for it.  The two instances together show that a resolution threshold is a
property of the chosen transverse channel, not of the carrier. -/

/-- The enlarged lane symmetry acts transitively on the six cover points. -/
theorem su2_transitive (x y : AxisLift) : ∃ g, y = GaugeSU2.actCover g x := by
  revert x y; decide

/-- Hence its transverse certificate is constant. -/
theorem su2_cert_constant (x y : AxisLift) :
    GaugeSU2.su2GaugeObserver.nondegeneracy x = GaugeSU2.su2GaugeObserver.nondegeneracy y := by
  obtain ⟨g, rfl⟩ := su2_transitive x y
  exact (GaugeSU2.su2GaugeObserver.nondegeneracy_invariant g x).symm

/-- The gauge-reduced lane's tower, with the same two coarsenings. -/
noncomputable def su2Tower : LayerTower :=
  twoStepTower GaugeSU2.su2GaugeObserver.reduction.proj axisMerge

/-- Its certificate factors at every level. -/
instance : Nonempty AxisLift := ⟨(.axisLow, .pos)⟩

theorem su2_cert_factorsAt (k : ℕ) :
    su2Tower.FactorsAt GaugeSU2.su2GaugeObserver.nondegeneracy k :=
  factorsAt_all_of_transitive GaugeSU2.su2GaugeObserver
    (fun x y => su2_transitive x y) axisMerge k

/-- So it has no coarsest sufficient level: nothing about observational
resolution can be read off a certificate whose symmetry is transitive. -/
theorem su2_no_coarsest :
    ¬ ∃ k, su2Tower.CoarsestSufficient GaugeSU2.su2GaugeObserver.nondegeneracy k := by
  rintro ⟨k, -, hk⟩
  exact hk (su2_cert_factorsAt (k + 1))

end Integration.DescentLevel
