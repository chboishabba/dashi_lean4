import Integration.SymmetryReduction
import Integration.ResidualQuotient
import Integration.PolarResidual
import Integration.SSPWeave
import Spine.Observer
import Spine.TernaryPhase

/-!
# The weld: symmetry-resolved observers

`Spine` proves geometry (fixed ⊕ transverse splitting, anchored Gram
coercivity, nondegeneracy certificates).  `Integration` proves reduction and
transport (equivariant quotients, residual-bearing quotients, the SSP lane
algebra).  Until now the two families of theorems were separate objects.  This
file makes them **one** object.

`SymmetryResolvedObserver G Rich Coarse Res n` bundles

* an `EquivariantQuotient G Rich Coarse` — a symmetry acting on the rich
  carrier, a coarse carrier, and the commuting square `π (g · x) = ḡ · π x`;
* a **reopenable residual** `Rich → Res` along the *same* projection, so the
  pair `(π x, residual x)` recovers `x` exactly;
* a **fixed/transverse representation**: a map of the rich carrier into
  `EuclideanSpace ℝ (Fin n)` together with a transverse channel, and a
  representation of `G` by inner-product-preserving maps that fix the constant
  direction `ones n`, intertwined with the rich action;
* two **nondegeneracy witnesses**: the reading has a nonzero constant mode and
  the channel a nonzero mean-zero part.

From those hypotheses the three promised conclusions are theorems
(`symmetry_resolved_theorem`):

1. *symmetry-compatible coarse dynamics* — `π (g · x) = ḡ · π x`, iterated
   along words (`SymmetryReduction.square_mul`), with `π` surjective;
2. *faithful fine-state recovery* — `reopen (π x) (residual x) = x`, the pair
   map is injective, and the residual is not removable whenever the coarse
   layer is strictly smaller (`residual_not_subsingleton`);
3. *a positive invariant on genuine transverse motion* — the anchored Gram
   area `area2 (read x) (fluct (channel x))` is strictly positive
   (`nondegeneracy_pos`, inherited from `Spine.MeanObserver`) **and** constant
   along the symmetry (`nondegeneracy_invariant`), so it is an invariant of the
   reduction, not merely of a chart.

Point 3 is the actual weld: the geometric certificate of `Spine` is proved to
be a function on `G`-orbits, which is what lets a `Spine` theorem be quoted
about a reduced `Integration` carrier.

## The instance: the SSP / 369 lane

`ssp369Observer` is the first inhabitant, built from the corpus's own SSP
material:

* `Rich` = the nine full phase cells `KernelTrit × DepthWheelPhase` of
  `SSP369PolarResidualQuotient`;
* `G` = the SSP `FibreOrientation` monoid of `SSPIndexedWeaveHyperfabricExact`,
  acting by polarity reversal on the kernel trit;
* `Coarse` = `KernelTrit`, the visible lane polarity, with **nontrivial**
  induced action (the hub polarity involution);
* `Res` = `DepthWheelPhase`, the retained phase residual;
* the representation is the permutation representation of the orientation on
  the nine cells, which fixes `ones 9`, and the reading is
  `ones + e_cell` with the phase-column indicator as transverse channel.

Two further theorems pin down *why* the residual has to be retained in the
target of an equivariant reduction:

* `polar6_no_equivariant_action` — the `9 → 6` polar projection admits **no**
  coarse action at all making the polarity square commute (the zero branch is
  parked on the negative sheet, so the origin is not symmetric).  This is the
  same failure mode as `SymmetryReduction.support_no_equivariant_action`.
* `polarResultReduction` — the residual-bearing `9 → 6 + 3` projection *is* an
  equivariant quotient, with nontrivial induced action.  So retaining the
  residual in the target is exactly what repairs equivariance:
  *equivariant reduction + retained residual = lossless symmetry-aware
  compression*, here as a checked statement rather than a slogan.

Scope.  Every carrier here is finite (9, 6, 3, 3, 2 elements) or a
nine-dimensional real inner product space.  `SSP` is used only as the corpus's
fifteen-element index set.  Nothing in this file asserts a physical claim, and
no Yang–Mills or Navier–Stokes material is imported.
-/

open RealInnerProductSpace

namespace Integration.StructuredObserver

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.PhaseQuotient (Phase3)
open Integration.Residual
open Integration.PolarResidual
open Integration.SSPWeave

/-! ## Representations by isometries fixing the constant direction -/

/-- A representation of `G` on `EuclideanSpace ℝ (Fin n)` by linear maps that
preserve the inner product and fix the constant direction `ones n`.  Fixing
`ones` is what makes the representation compatible with the fixed ⊕ transverse
splitting: it forces the mean and the fluctuation to be transported
separately. -/
structure FixedIsometryRep (G : Type) (n : ℕ) [NeZero n] where
  /-- The action on the structured carrier. -/
  act : G → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  /-- Each `act g` preserves the inner product. -/
  inner_map : ∀ g x y, ⟪act g x, act g y⟫ = ⟪x, y⟫
  /-- Each `act g` fixes the constant direction. -/
  ones_fixed : ∀ g, act g (ones n) = ones n
  /-- Each `act g` is additive (stated on differences). -/
  map_sub : ∀ g x y, act g (x - y) = act g x - act g y
  /-- Each `act g` is homogeneous. -/
  map_smul : ∀ g (c : ℝ) x, act g (c • x) = c • act g x

namespace FixedIsometryRep

variable {G : Type} {n : ℕ} [NeZero n] (R : FixedIsometryRep G n)

theorem norm_sq_map (g : G) (x : EuclideanSpace ℝ (Fin n)) : ‖R.act g x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, R.inner_map]

omit [NeZero n] in
/-- The mean of a vector is its inner product with the constant direction. -/
theorem avg_eq_inner (x : EuclideanSpace ℝ (Fin n)) : avg x = ⟪ones n, x⟫ / n := by
  rw [inner_eq_sum]
  simp [avg]

/-- Because the representation fixes `ones`, it preserves the mean. -/
theorem avg_map (g : G) (x : EuclideanSpace ℝ (Fin n)) : avg (R.act g x) = avg x := by
  have h : ⟪ones n, R.act g x⟫ = ⟪ones n, x⟫ :=
    calc ⟪ones n, R.act g x⟫ = ⟪R.act g (ones n), R.act g x⟫ := by rw [R.ones_fixed]
      _ = ⟪ones n, x⟫ := R.inner_map g _ _
  rw [avg_eq_inner, avg_eq_inner, h]

/-- Hence it preserves the fixed component. -/
theorem meanPart_map (g : G) (x : EuclideanSpace ℝ (Fin n)) :
    meanPart (R.act g x) = R.act g (meanPart x) := by
  rw [meanPart, meanPart, R.map_smul, R.ones_fixed, R.avg_map]

/-- And therefore commutes with the transverse projection: the fixed ⊕
transverse splitting is a splitting of `G`-representations. -/
theorem fluct_map (g : G) (x : EuclideanSpace ℝ (Fin n)) :
    fluct (R.act g x) = R.act g (fluct x) := by
  rw [fluct, fluct, R.map_sub, R.meanPart_map]

/-- The transverse area is a representation invariant. -/
theorem area2_map (g : G) (x y : EuclideanSpace ℝ (Fin n)) :
    area2 (R.act g x) (R.act g y) = area2 x y := by
  simp [area2, R.norm_sq_map, R.inner_map]

end FixedIsometryRep

/-! ## The welded structure -/

/-- A **symmetry-resolved observer**: an equivariant quotient, a reopenable
residual along the same projection, a fixed/transverse representation
intertwined with the symmetry, and the two nondegeneracy witnesses.  This is the
single object carrying both the `Integration` transport theorems and the `Spine`
geometry theorems. -/
structure SymmetryResolvedObserver (G Rich Coarse Res : Type) [Monoid G]
    (n : ℕ) [NeZero n] where
  /-- The symmetry reduction: action, coarse action and the commuting square. -/
  reduction : EquivariantQuotient G Rich Coarse
  /-- The retained residual. -/
  residual : Rich → Res
  /-- Reassembly of the rich state from coarse datum and residual. -/
  reopen : Coarse → Res → Rich
  /-- Reassembly is exact: the reduction is lossless once the residual is kept. -/
  reopen_project : ∀ x, reopen (reduction.proj x) (residual x) = x
  /-- The representation of the symmetry on the structured carrier. -/
  rep : FixedIsometryRep G n
  /-- The reading of a rich state into the structured carrier. -/
  read : Rich → EuclideanSpace ℝ (Fin n)
  /-- The transverse channel. -/
  channel : Rich → EuclideanSpace ℝ (Fin n)
  /-- The reading intertwines the two actions. -/
  read_equivariant : ∀ g x, read (reduction.actRich g x) = rep.act g (read x)
  /-- So does the channel. -/
  channel_equivariant : ∀ g x, channel (reduction.actRich g x) = rep.act g (channel x)
  /-- Nondegeneracy witness 1: the reading has a nonzero constant mode. -/
  mean_ne_zero : ∀ x, avg (read x) ≠ 0
  /-- Nondegeneracy witness 2: the channel has a nonzero transverse part. -/
  fluct_ne_zero : ∀ x, fluct (channel x) ≠ 0

namespace SymmetryResolvedObserver

variable {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
  (O : SymmetryResolvedObserver G Rich Coarse Res n)

/-- The residual-bearing quotient carried by a symmetry-resolved observer. -/
def toResidualQuotient : ResidualQuotient Rich Coarse Res where
  project := O.reduction.proj
  residual := O.residual
  reopen := O.reopen
  reopen_project := O.reopen_project

/-- The mean observer carried by a symmetry-resolved observer. -/
def toMeanObserver : Spine.MeanObserver Rich n where
  read := O.read
  channel := O.channel
  mean_ne_zero := O.mean_ne_zero
  fluct_ne_zero := O.fluct_ne_zero

/-! ### Conclusion 1: symmetry-compatible coarse dynamics -/

theorem coarse_dynamics (g : G) (x : Rich) :
    O.reduction.proj (O.reduction.actRich g x) = O.reduction.actCoarse g (O.reduction.proj x) :=
  O.reduction.square g x

theorem coarse_dynamics_word (g h : G) (x : Rich) :
    O.reduction.proj (O.reduction.actRich g (O.reduction.actRich h x))
      = O.reduction.actCoarse g (O.reduction.actCoarse h (O.reduction.proj x)) :=
  square_mul O.reduction g h x

theorem coarse_surjective : Function.Surjective O.reduction.proj :=
  O.reduction.proj_surjective

/-! ### Conclusion 2: faithful fine-state recovery -/

theorem fine_recovery (x : Rich) : O.reopen (O.reduction.proj x) (O.residual x) = x :=
  O.reopen_project x

theorem coarse_residual_injective :
    Function.Injective (fun x => (O.reduction.proj x, O.residual x)) :=
  injective_pair (toResidualQuotient O)

include O in
/-- The residual is not removable bookkeeping whenever the coarse layer is
strictly smaller than the rich one. -/
theorem residual_nontrivial [Fintype Rich] [Fintype Coarse] [Fintype Res]
    (h : Fintype.card Coarse < Fintype.card Rich) : 2 ≤ Fintype.card Res :=
  residual_not_subsingleton (toResidualQuotient O) h

/-! ### Conclusion 3: a positive, symmetry-invariant transverse certificate -/

/-- The nondegeneracy certificate: the squared transverse area swept by the
reading and the channel's transverse part. -/
noncomputable def nondegeneracy (x : Rich) : ℝ := area2 (O.read x) (fluct (O.channel x))

/-- **Spine side.**  The certificate is strictly positive: the observed pair
spans a genuine plane, not two labels. -/
theorem nondegeneracy_pos (x : Rich) : 0 < O.nondegeneracy x :=
  Spine.MeanObserver.transverse_area_pos O.toMeanObserver x

/-- **The weld.**  The certificate is constant along the symmetry, so it is an
invariant of the reduction rather than of the chart. -/
theorem nondegeneracy_invariant (g : G) (x : Rich) :
    O.nondegeneracy (O.reduction.actRich g x) = O.nondegeneracy x := by
  simp only [nondegeneracy, O.read_equivariant, O.channel_equivariant,
    O.rep.fluct_map, O.rep.area2_map]

/-- Consequently the certificate is constant on `G`-orbits. -/
theorem nondegeneracy_orbit_constant {x y : Rich} (h : ∃ g, y = O.reduction.actRich g x) :
    O.nondegeneracy y = O.nondegeneracy x := by
  obtain ⟨g, rfl⟩ := h
  exact O.nondegeneracy_invariant g x

/-! ### The three conclusions in one statement -/

/-- **The welded theorem.**  Equivariant quotient + reopenable residual +
fixed/transverse representation + transverse nondegeneracy imply
symmetry-compatible coarse dynamics, faithful fine-state recovery, and a
strictly positive invariant on the transverse motion. -/
theorem symmetry_resolved_theorem :
    (Function.Surjective O.reduction.proj ∧
        ∀ g x, O.reduction.proj (O.reduction.actRich g x)
          = O.reduction.actCoarse g (O.reduction.proj x)) ∧
      (∀ x, O.reopen (O.reduction.proj x) (O.residual x) = x) ∧
      Function.Injective (fun x => (O.reduction.proj x, O.residual x)) ∧
      (∀ x, 0 < O.nondegeneracy x) ∧
      (∀ g x, O.nondegeneracy (O.reduction.actRich g x) = O.nondegeneracy x) :=
  ⟨⟨O.coarse_surjective, O.coarse_dynamics⟩, O.fine_recovery, O.coarse_residual_injective,
    O.nondegeneracy_pos, O.nondegeneracy_invariant⟩

end SymmetryResolvedObserver

/-! ## A reusable constructor for symmetry-resolved observers

Every corpus instance of the welded record so far has the same shape: a finite
rich carrier, an action by bijections, a projection with a reopenable residual,
and a `G`-invariant class function used as the transverse channel.  This section
turns that shape into one constructor, so a domain earns its instantiation by
supplying finite data and four small proofs rather than by rebuilding the
geometry.

The class function `cls` is the transverse coordinate: the channel of a state is
the indicator of its `cls`-class.  In a reduction whose *coarse* layer moves
(the SSP lane, the NS Stage-3 ledger) one takes `cls = residual`; in a reduction
whose *fibre* moves (a double cover, where the base is invariant) one takes
`cls = proj`.  Both are covered by the same theorem. -/

@[simp] theorem lp_coord_apply {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n)) j = f j := rfl

/-- Finite data from which a symmetry-resolved observer can be built: an
equivariant quotient whose action is by bijections, a reopenable residual, and a
`G`-invariant, non-constant class function to serve as the transverse channel. -/
structure ObserverBuild (G Rich Coarse Res K : Type) [Monoid G] where
  /-- The symmetry reduction. -/
  reduction : EquivariantQuotient G Rich Coarse
  /-- The inverse of each action map. -/
  actInv : G → Rich → Rich
  /-- `actInv g` is a left inverse of `actRich g`. -/
  actInv_left : ∀ g x, actInv g (reduction.actRich g x) = x
  /-- `actInv g` is a right inverse of `actRich g`. -/
  actInv_right : ∀ g x, reduction.actRich g (actInv g x) = x
  /-- The retained residual. -/
  residual : Rich → Res
  /-- The reassembly map. -/
  reopen : Coarse → Res → Rich
  /-- Reassembly is exact. -/
  reopen_project : ∀ x, reopen (reduction.proj x) (residual x) = x
  /-- The transverse class coordinate. -/
  cls : Rich → K
  /-- The class coordinate is a symmetry invariant. -/
  cls_invariant : ∀ g x, cls (reduction.actRich g x) = cls x
  /-- And it is non-constant, so the channel is genuinely transverse. -/
  cls_separates : ∀ x, ∃ y, cls y ≠ cls x

namespace ObserverBuild

variable {G Rich Coarse Res K : Type} [Monoid G] [DecidableEq K] {n : ℕ} [NeZero n]

omit [DecidableEq K] in
theorem cls_invariant_inv (B : ObserverBuild G Rich Coarse Res K) (g : G) (x : Rich) :
    B.cls (B.actInv g x) = B.cls x := by
  have h := B.cls_invariant g (B.actInv g x)
  rw [B.actInv_right] at h
  exact h.symm

/-- The permutation of coordinates induced by `g`.  It is the *inverse* action
that permutes coordinates, which is what makes the reading equivariant. -/
def perm (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n) (g : G) :
    Equiv.Perm (Fin n) where
  toFun j := enum (B.actInv g (enum.symm j))
  invFun j := enum (B.reduction.actRich g (enum.symm j))
  left_inv j := by simp [B.actInv_right]
  right_inv j := by simp [B.actInv_left]

omit [DecidableEq K] [NeZero n] in
@[simp] theorem perm_apply (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (g : G) (j : Fin n) : perm B enum g j = enum (B.actInv g (enum.symm j)) := rfl

/-- The permutation representation of `G` on the coordinates. -/
noncomputable def rep (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n) :
    FixedIsometryRep G n where
  act g x := WithLp.toLp 2 (fun j => x (perm B enum g j))
  inner_map g x y := by
    rw [inner_eq_sum, inner_eq_sum]
    simpa using Equiv.sum_comp (perm B enum g) (fun j => x j * y j)
  ones_fixed g := by ext j; simp
  map_sub g x y := by ext j; simp
  map_smul g c x := by ext j; simp

/-- The reading: the constant vector plus the indicator of the state. -/
noncomputable def readVec (enum : Rich ≃ Fin n) (x : Rich) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => 1 + (if j = enum x then (1 : ℝ) else 0))

/-- The transverse channel: the indicator of the state's class. -/
noncomputable def channelVec (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (x : Rich) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if B.cls (enum.symm j) = B.cls x then (1 : ℝ) else 0)

omit [DecidableEq K] in
theorem readVec_equivariant (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (g : G) (x : Rich) :
    readVec enum (B.reduction.actRich g x) = (rep B enum).act g (readVec enum x) := by
  ext j
  show 1 + (if j = enum (B.reduction.actRich g x) then (1 : ℝ) else 0)
      = 1 + (if perm B enum g j = enum x then (1 : ℝ) else 0)
  have key : (j = enum (B.reduction.actRich g x)) ↔ (perm B enum g j = enum x) := by
    constructor
    · rintro rfl
      simp [B.actInv_left]
    · intro hj
      have h1 : B.actInv g (enum.symm j) = x := enum.injective hj
      have h2 : enum.symm j = B.reduction.actRich g x := by rw [← h1, B.actInv_right]
      rw [← h2, Equiv.apply_symm_apply]
  exact congrArg _ (if_congr key rfl rfl)

theorem channelVec_equivariant (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (g : G) (x : Rich) :
    channelVec B enum (B.reduction.actRich g x) = (rep B enum).act g (channelVec B enum x) := by
  ext j
  show (if B.cls (enum.symm j) = B.cls (B.reduction.actRich g x) then (1 : ℝ) else 0)
      = (if B.cls (enum.symm (perm B enum g j)) = B.cls x then (1 : ℝ) else 0)
  rw [B.cls_invariant, perm_apply, Equiv.symm_apply_apply, cls_invariant_inv]

omit [NeZero n] in
theorem avg_readVec (enum : Rich ≃ Fin n) (x : Rich) :
    avg (readVec enum x) = ((n : ℝ) + 1) / n := by
  have hsum : ∑ j : Fin n, (1 + (if j = enum x then (1 : ℝ) else 0)) = (n : ℝ) + 1 := by
    rw [Finset.sum_add_distrib]
    simp
  simp only [avg, readVec, lp_coord_apply]
  rw [hsum]

theorem avg_readVec_ne_zero (enum : Rich ≃ Fin n) (x : Rich) : avg (readVec enum x) ≠ 0 := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have h : (n : ℕ) ≠ 0 := NeZero.ne n
    exact_mod_cast Nat.pos_of_ne_zero h
  rw [avg_readVec]
  positivity

theorem fluct_channelVec_ne_zero (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (x : Rich) : fluct (channelVec B enum x) ≠ 0 := by
  intro h
  obtain ⟨y, hy⟩ := B.cls_separates x
  have hc := (fluct_eq_zero_iff (channelVec B enum x)).mp h (enum x) (enum y)
  simp only [channelVec, lp_coord_apply, Equiv.symm_apply_apply] at hc
  simp [hy] at hc

/-- **The constructor.**  Finite data plus four small proofs give a
symmetry-resolved observer, hence all three welded conclusions. -/
noncomputable def toObserver (B : ObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n) :
    SymmetryResolvedObserver G Rich Coarse Res n where
  reduction := B.reduction
  residual := B.residual
  reopen := B.reopen
  reopen_project := B.reopen_project
  rep := rep B enum
  read := readVec enum
  channel := channelVec B enum
  read_equivariant := readVec_equivariant B enum
  channel_equivariant := channelVec_equivariant B enum
  mean_ne_zero := avg_readVec_ne_zero enum
  fluct_ne_zero := fluct_channelVec_ne_zero B enum

end ObserverBuild


/-! ### Controls: the two witness families are load-bearing

Neither half of the welded record can be dropped.  If the transverse channel is
constant the certificate is zero, so the geometric conclusion is vacuous without
the nondegeneracy witness; and a chart whose origin is not symmetric admits no
coarse action at all, so the transport conclusion is unavailable without the
equivariance witness (`polar6_no_equivariant_action`, below). -/

/-- A constant channel gives a zero certificate: the nondegeneracy witness is
what makes the third conclusion say anything. -/
theorem certificate_zero_of_constant_channel {n : ℕ} [NeZero n]
    (x y : EuclideanSpace ℝ (Fin n)) (hy : ∀ i j, y i = y j) : area2 x (fluct y) = 0 :=
  Spine.degenerate_observer_area_zero x y hy

/-! ## The SSP / 369 instance

The nine full phase cells, the SSP orientation monoid acting by polarity
reversal, the visible lane polarity as coarse layer, and the depth-wheel phase
as retained residual. -/

/-- The SSP orientation acting on the nine full phase cells: `inverse` reverses
the kernel polarity, the other two orientations act trivially (they have sign
`0` in `orientationSign`). -/
def actFull : FibreOrientation → FullPhaseCell → FullPhaseCell
  | .inverse, (t, ph) => (negateTrit t, ph)
  | .mediated, c => c
  | .forward, c => c

/-- The induced action on the visible lane polarity. -/
def actKernel : FibreOrientation → KernelTrit → KernelTrit
  | .inverse, t => negateTrit t
  | .mediated, t => t
  | .forward, t => t

theorem actFull_one (c : FullPhaseCell) : actFull 1 c = c := by
  obtain ⟨t, ph⟩ := c; rfl

theorem actFull_mul (g h : FibreOrientation) (c : FullPhaseCell) :
    actFull (g * h) c = actFull g (actFull h c) := by
  revert g h c; decide

theorem actKernel_one (t : KernelTrit) : actKernel 1 t = t := rfl

theorem actKernel_mul (g h : FibreOrientation) (t : KernelTrit) :
    actKernel (g * h) t = actKernel g (actKernel h t) := by
  revert g h t; decide

/-- **The visible reduction `9 → 3`.**  The lane polarity is an equivariant
quotient of the nine cells, with the polarity involution as induced action —
so the coarse action is *not* trivial: this is a symmetry-compatible
observation, not an orbit map. -/
def kernelReduction : EquivariantQuotient FibreOrientation FullPhaseCell KernelTrit where
  actRich := actFull
  actCoarse := actKernel
  proj := Prod.fst
  rich_one := actFull_one
  rich_mul := actFull_mul
  coarse_one := actKernel_one
  coarse_mul := actKernel_mul
  proj_surjective := by decide
  square := by decide

theorem kernelReduction_action_nontrivial :
    ∃ g t, kernelReduction.actCoarse g t ≠ t :=
  ⟨.inverse, .negativeTrit, by decide⟩

/-! ### The nine cells as coordinates -/

/-- The nine full phase cells, enumerated. -/
def cellOf : Fin 9 → FullPhaseCell :=
  ![(.negativeTrit, .phase0), (.negativeTrit, .phase1), (.negativeTrit, .phase2),
    (.zeroTrit, .phase0), (.zeroTrit, .phase1), (.zeroTrit, .phase2),
    (.positiveTrit, .phase0), (.positiveTrit, .phase1), (.positiveTrit, .phase2)]

/-- The index of a full phase cell. -/
def cellIdx : FullPhaseCell → Fin 9
  | (.negativeTrit, .phase0) => 0
  | (.negativeTrit, .phase1) => 1
  | (.negativeTrit, .phase2) => 2
  | (.zeroTrit, .phase0) => 3
  | (.zeroTrit, .phase1) => 4
  | (.zeroTrit, .phase2) => 5
  | (.positiveTrit, .phase0) => 6
  | (.positiveTrit, .phase1) => 7
  | (.positiveTrit, .phase2) => 8

theorem cellOf_cellIdx (c : FullPhaseCell) : cellOf (cellIdx c) = c := by
  revert c; decide

theorem cellIdx_cellOf (j : Fin 9) : cellIdx (cellOf j) = j := by
  revert j; decide

/-- The permutation of the nine coordinates induced by an orientation. -/
def cellPerm (g : FibreOrientation) : Equiv.Perm (Fin 9) where
  toFun j := cellIdx (actFull g (cellOf j))
  invFun j := cellIdx (actFull g (cellOf j))
  left_inv := by revert g; decide
  right_inv := by revert g; decide

@[simp] theorem coord_apply (f : Fin 9 → ℝ) (j : Fin 9) :
    (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin 9)) j = f j := rfl

/-- The permutation representation of the orientation monoid on `ℝ⁹`. -/
noncomputable def cellRep : FixedIsometryRep FibreOrientation 9 where
  act g x := WithLp.toLp 2 (fun j => x (cellPerm g j))
  inner_map g x y := by
    rw [inner_eq_sum, inner_eq_sum]
    simpa using Equiv.sum_comp (cellPerm g) (fun j => x j * y j)
  ones_fixed g := by ext j; simp
  map_sub g x y := by ext j; simp
  map_smul g c x := by ext j; simp

/-- The reading: the constant vector plus the indicator of the cell.  Its mean
is `10/9 ≠ 0`, so the fixed mode is nondegenerate. -/
noncomputable def readCell (c : FullPhaseCell) : EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 (fun j => 1 + (if j = cellIdx c then (1 : ℝ) else 0))

/-- The transverse channel: the indicator of the phase column of the cell — the
three cells sharing its depth-wheel phase.  This is the residual coordinate seen
inside the structured carrier. -/
noncomputable def channelCell (c : FullPhaseCell) : EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 (fun j => if (cellOf j).2 = c.2 then (1 : ℝ) else 0)

theorem read_key (g : FibreOrientation) (c : FullPhaseCell) (j : Fin 9) :
    (j = cellIdx (actFull g c)) ↔ (cellPerm g j = cellIdx c) := by
  revert g c j; decide

theorem channel_key (g : FibreOrientation) (c : FullPhaseCell) (j : Fin 9) :
    ((cellOf j).2 = c.2) ↔ ((cellOf (cellPerm g j)).2 = c.2) := by
  revert g c j; decide

theorem readCell_equivariant (g : FibreOrientation) (c : FullPhaseCell) :
    readCell (actFull g c) = cellRep.act g (readCell c) := by
  ext j
  show 1 + (if j = cellIdx (actFull g c) then (1 : ℝ) else 0)
      = 1 + (if cellPerm g j = cellIdx c then (1 : ℝ) else 0)
  rw [if_congr (read_key g c j) rfl rfl]

theorem channelCell_equivariant (g : FibreOrientation) (c : FullPhaseCell) :
    channelCell (actFull g c) = cellRep.act g (channelCell c) := by
  ext j
  have hph : (actFull g c).2 = c.2 := by revert g c; decide
  show (if (cellOf j).2 = (actFull g c).2 then (1 : ℝ) else 0)
      = (if (cellOf (cellPerm g j)).2 = c.2 then (1 : ℝ) else 0)
  rw [hph, if_congr (channel_key g c j) rfl rfl]

theorem avg_readCell (c : FullPhaseCell) : avg (readCell c) = 10 / 9 := by
  have hsum : ∑ j : Fin 9, (1 + (if j = cellIdx c then (1 : ℝ) else 0)) = 10 := by
    rw [Finset.sum_add_distrib]
    simp
    norm_num
  simp only [avg, readCell, coord_apply]
  rw [hsum]
  norm_num

theorem avg_readCell_ne_zero (c : FullPhaseCell) : avg (readCell c) ≠ 0 := by
  rw [avg_readCell]; norm_num

theorem next_phase_ne (p : DepthWheelPhase) : nextDepthWheelPhase p ≠ p := by
  cases p <;> decide

theorem fluct_channelCell_ne_zero (c : FullPhaseCell) : fluct (channelCell c) ≠ 0 := by
  intro h
  have hc := (fluct_eq_zero_iff (channelCell c)).mp h
    (cellIdx (.negativeTrit, c.2)) (cellIdx (.negativeTrit, nextDepthWheelPhase c.2))
  simp only [channelCell, coord_apply, cellOf_cellIdx] at hc
  simp [next_phase_ne c.2] at hc

/-- **The SSP / 369 symmetry-resolved observer.**  Nine rich states, the SSP
orientation monoid, a three-state visible lane polarity with nontrivial induced
action, a three-state retained phase residual, and a nine-dimensional
fixed/transverse representation in which the orientation acts by an isometry
fixing the constant direction. -/
noncomputable def ssp369Observer :
    SymmetryResolvedObserver FibreOrientation FullPhaseCell KernelTrit DepthWheelPhase 9 where
  reduction := kernelReduction
  residual := Prod.snd
  reopen := fun t ph => (t, ph)
  reopen_project := fun _ => rfl
  rep := cellRep
  read := readCell
  channel := channelCell
  read_equivariant := readCell_equivariant
  channel_equivariant := channelCell_equivariant
  mean_ne_zero := avg_readCell_ne_zero
  fluct_ne_zero := fluct_channelCell_ne_zero

/-- The three conclusions, instantiated on the SSP lane. -/
theorem ssp369_theorem :
    (Function.Surjective ssp369Observer.reduction.proj ∧
        ∀ g x, ssp369Observer.reduction.proj (ssp369Observer.reduction.actRich g x)
          = ssp369Observer.reduction.actCoarse g (ssp369Observer.reduction.proj x)) ∧
      (∀ x, ssp369Observer.reopen (ssp369Observer.reduction.proj x)
        (ssp369Observer.residual x) = x) ∧
      Function.Injective
        (fun x => (ssp369Observer.reduction.proj x, ssp369Observer.residual x)) ∧
      (∀ x, 0 < ssp369Observer.nondegeneracy x) ∧
      (∀ g x, ssp369Observer.nondegeneracy (ssp369Observer.reduction.actRich g x)
        = ssp369Observer.nondegeneracy x) :=
  ssp369Observer.symmetry_resolved_theorem

/-- On the SSP lane the residual is forced: three visible polarities cannot
carry nine states, so the retained phase has at least two values. -/
theorem ssp369_residual_nontrivial : 2 ≤ Fintype.card DepthWheelPhase :=
  SymmetryResolvedObserver.residual_nontrivial ssp369Observer (by decide)


/-! ## Instance: a genuine `C₃` symmetry-resolved observer

The instances above all act through the effective `ℤ/2` of the orientation
monoid.  This one acts through an honest order-three group: the depth wheel of
the same nine-cell carrier, rotated by `Phase3`.  The visible layer is the lane
polarity (invariant, so this is an orbit reduction) and the residual is the
phase itself.

The section closes by connecting the wheel to the spine's `C₃` representation:
`phaseEmbed` intertwines `nextDepthWheelPhase` with `Spine.RealC3.shift`, so the
corpus's depth wheel *is* a copy of `ℝ[C₃]`, and the spine's theorems about the
transverse plane (irreducible, no real eigenline) apply to it. -/

/-- Rotation of the depth wheel by an element of `Phase3`. -/
def rotPhase : Phase3 → DepthWheelPhase → DepthWheelPhase
  | .p0, ph => ph
  | .p1, ph => nextDepthWheelPhase ph
  | .p2, ph => nextDepthWheelPhase (nextDepthWheelPhase ph)

/-- The `C₃` action on the nine cells: rotate the phase, fix the polarity. -/
def actWheel : Phase3 → FullPhaseCell → FullPhaseCell
  | g, (t, ph) => (t, rotPhase g ph)

/-- The inverse rotation. -/
def invPhase : Phase3 → Phase3
  | .p0 => .p0 | .p1 => .p2 | .p2 => .p1

theorem actWheel_one (c : FullPhaseCell) : actWheel 1 c = c := by
  obtain ⟨t, ph⟩ := c; rfl

theorem actWheel_mul (g h : Phase3) (c : FullPhaseCell) :
    actWheel (g * h) c = actWheel g (actWheel h c) := by
  revert g h c; decide

theorem actWheel_invPhase_left (g : Phase3) (c : FullPhaseCell) :
    actWheel (invPhase g) (actWheel g c) = c := by
  revert g c; decide

theorem actWheel_invPhase_right (g : Phase3) (c : FullPhaseCell) :
    actWheel g (actWheel (invPhase g) c) = c := by
  revert g c; decide

/-- **Order three, and free.**  The generator is not the identity on any state,
and its cube is. -/
theorem actWheel_order_three (c : FullPhaseCell) :
    actWheel .p1 (actWheel .p1 (actWheel .p1 c)) = c ∧ actWheel .p1 c ≠ c := by
  revert c; decide

/-- The `C₃` reduction `9 → 3`: the lane polarity is invariant under the wheel,
so the visible layer is the orbit space of the phase rotation. -/
def wheelReduction : EquivariantQuotient Phase3 FullPhaseCell KernelTrit where
  actRich := actWheel
  actCoarse := fun _ t => t
  proj := Prod.fst
  rich_one := actWheel_one
  rich_mul := actWheel_mul
  coarse_one := fun _ => rfl
  coarse_mul := fun _ _ _ => rfl
  proj_surjective := by decide
  square := by decide

/-- Observer data for the wheel: the residual is the phase (which moves), so the
transverse class is the invariant polarity. -/
def wheelBuild : ObserverBuild Phase3 FullPhaseCell KernelTrit DepthWheelPhase KernelTrit where
  reduction := wheelReduction
  actInv := fun g => actWheel (invPhase g)
  actInv_left := actWheel_invPhase_left
  actInv_right := actWheel_invPhase_right
  residual := Prod.snd
  reopen := fun t ph => (t, ph)
  reopen_project := fun _ => rfl
  cls := Prod.fst
  cls_invariant := by decide
  cls_separates := by decide

/-- The nine cells as coordinates, as an equivalence. -/
def cellEquiv : FullPhaseCell ≃ Fin 9 where
  toFun := cellIdx
  invFun := cellOf
  left_inv := cellOf_cellIdx
  right_inv := cellIdx_cellOf

/-- **A symmetry-resolved observer for an order-three symmetry.** -/
noncomputable def wheelObserver :
    SymmetryResolvedObserver Phase3 FullPhaseCell KernelTrit DepthWheelPhase 9 :=
  wheelBuild.toObserver cellEquiv

/-- The three welded conclusions for the `C₃` wheel. -/
theorem wheel_theorem :
    (Function.Surjective wheelObserver.reduction.proj ∧
        ∀ g x, wheelObserver.reduction.proj (wheelObserver.reduction.actRich g x)
          = wheelObserver.reduction.actCoarse g (wheelObserver.reduction.proj x)) ∧
      (∀ x, wheelObserver.reopen (wheelObserver.reduction.proj x)
        (wheelObserver.residual x) = x) ∧
      Function.Injective
        (fun x => (wheelObserver.reduction.proj x, wheelObserver.residual x)) ∧
      (∀ x, 0 < wheelObserver.nondegeneracy x) ∧
      (∀ g x, wheelObserver.nondegeneracy (wheelObserver.reduction.actRich g x)
        = wheelObserver.nondegeneracy x) :=
  wheelObserver.symmetry_resolved_theorem

/-! ### The wheel is the spine's `ℝ[C₃]` -/

/-- The depth-wheel phase as a coordinate index. -/
def phaseIdx : DepthWheelPhase → Fin 3
  | .phase0 => 0 | .phase1 => 1 | .phase2 => 2

/-- Its inverse. -/
def phaseOfIdx : Fin 3 → DepthWheelPhase :=
  ![.phase0, .phase1, .phase2]

/-- A real function on the depth wheel, read in the spine's `C₃` carrier. -/
noncomputable def phaseEmbed (f : DepthWheelPhase → ℝ) : Spine.RealC3.V :=
  WithLp.toLp 2 (fun i => f (phaseOfIdx i))

/-- **The depth wheel is a copy of `ℝ[C₃]`.**  The corpus's phase successor is
intertwined with the spine's cyclic shift, so every spine theorem about the
`C₃` fixed line and its irreducible transverse plane applies to the wheel. -/
theorem phaseEmbed_rot (f : DepthWheelPhase → ℝ) :
    Spine.RealC3.shift (phaseEmbed f) = phaseEmbed (f ∘ nextDepthWheelPhase) := by
  ext i
  fin_cases i <;> rfl

/-- Consequently the wheel's transverse plane carries no invariant line: the
rotation of a nonzero mean-zero phase profile is never a multiple of it. -/
theorem wheel_no_invariant_line (x : Spine.RealC3.V) (hx : x ∈ Spine.RealC3.transverse)
    (hx0 : x ≠ 0) (c : ℝ) : Spine.RealC3.shift x ≠ c • x :=
  Spine.RealC3.no_real_eigenvector_transverse hx hx0 c

/-- The `C₃` tranche in one statement: an order-three free action on the nine
cells, its welded conclusions, and its identification with the spine's `C₃`
representation. -/
theorem wheel_c3_summary :
    (∀ c : FullPhaseCell,
        actWheel .p1 (actWheel .p1 (actWheel .p1 c)) = c ∧ actWheel .p1 c ≠ c) ∧
      (∀ x, 0 < wheelObserver.nondegeneracy x) ∧
      (∀ g x, wheelObserver.nondegeneracy (wheelObserver.reduction.actRich g x)
        = wheelObserver.nondegeneracy x) ∧
      (∀ f : DepthWheelPhase → ℝ,
        Spine.RealC3.shift (phaseEmbed f) = phaseEmbed (f ∘ nextDepthWheelPhase)) :=
  ⟨actWheel_order_three, wheelObserver.nondegeneracy_pos,
    wheelObserver.nondegeneracy_invariant, phaseEmbed_rot⟩

/-! ### Why the residual must be retained *in the target*

The `9 → 6` polar projection is not an equivariant quotient at all, and the
`9 → 6 + 3` residual-bearing projection is. -/

/-- **Boundary.**  There is no map on the six polar cells whatsoever making the
polarity square commute for the `9 → 6` projection: the zero branch is parked on
the negative sheet, so the chart's origin is not symmetric.  (Same failure mode
as `SymmetryReduction.support_no_equivariant_action`.) -/
theorem polar6_no_equivariant_action :
    ¬ ∃ f : PolarPhaseCell → PolarPhaseCell,
        ∀ c : FullPhaseCell, polarCoarse (negateCell c) = f (polarCoarse c) := by
  rintro ⟨f, h⟩
  have h1 := h (.zeroTrit, .phase0)
  have h2 := h (.negativeTrit, .phase0)
  simp only [polarCoarse, negateCell, negateTrit] at h1 h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-- The coarse action on `6 + 3`: flip the polar sheet, fix the residual
branch. -/
def actResult : FibreOrientation → PolarProjectionResult → PolarProjectionResult
  | .inverse, r => negateResult r
  | .mediated, r => r
  | .forward, r => r

/-- **The repair.**  Keeping the residual in the target turns the same
projection into an equivariant quotient: `9 → 6 + 3` intertwines the polarity
action with the sheet flip. -/
def polarResultReduction :
    EquivariantQuotient FibreOrientation FullPhaseCell PolarProjectionResult where
  actRich := actFull
  actCoarse := actResult
  proj := polarProject
  rich_one := actFull_one
  rich_mul := actFull_mul
  coarse_one := fun r => by cases r <;> rfl
  coarse_mul := by decide
  proj_surjective := by decide
  square := by decide

theorem polarResultReduction_action_nontrivial :
    ∃ g r, polarResultReduction.actCoarse g r ≠ r :=
  ⟨.inverse, .projectedPolar (.polarNegative, .phase0), by decide⟩

/-- **Lossless symmetry-aware compression, as one statement.**  The `9 → 6`
projection admits no equivariant structure; the residual-bearing `9 → 6 + 3`
projection is equivariant, with nontrivial induced action, and is a bijection,
hence lossless. -/
theorem equivariant_reduction_plus_residual :
    (¬ ∃ f : PolarPhaseCell → PolarPhaseCell,
        ∀ c : FullPhaseCell, polarCoarse (negateCell c) = f (polarCoarse c)) ∧
      (∀ g c, polarProject (actFull g c) = actResult g (polarProject c)) ∧
      (∃ g r, actResult g r ≠ r) ∧
      (∀ c : FullPhaseCell, reopenPolarResult (polarProject c) = c) :=
  ⟨polar6_no_equivariant_action, polarResultReduction.square,
    polarResultReduction_action_nontrivial, reopen_project⟩

end Integration.StructuredObserver
