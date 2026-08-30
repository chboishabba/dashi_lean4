import Integration.StructuredObserver

/-!
# Transverse channels for symmetries that move every class

`Integration.StructuredObserver.ObserverBuild` builds a symmetry-resolved
observer from a class coordinate `cls` that is *invariant* under the symmetry:
the channel of a state is the indicator of its class, and invariance is what
makes the channel equivariant.  That is the right hypothesis when the coarse
layer is fixed by the symmetry, but it is unavailable exactly in the most
interesting case: when the symmetry acts transitively on the rich carrier, the
only invariant class functions are the constant ones, and a constant channel has
zero transverse area (`certificate_zero_of_constant_channel`).

This file weakens the hypothesis to what the geometry actually needs.  The class
coordinate is allowed to **move**, provided it moves by a bijection of the class
set intertwined with the symmetry:

```
cls (g · x) = ǧ · cls x .
```

Then the indicator of the class of `x` is still carried to the indicator of the
class of `g · x` by the permutation representation, so the channel is
equivariant and the welded theorem applies verbatim.

* `ActionChart` — an action by bijections together with an enumeration of the
  carrier; it produces the permutation representation `rep` on `ℝⁿ`, which fixes
  the constant vector and is orthogonal, and the reading `ones + eₓ`.
* `EqObserverBuild` — the same finite data as `ObserverBuild` but with an
  equivariant, rather than invariant, class coordinate.
* `EqObserverBuild.toObserver` — the resulting `SymmetryResolvedObserver`, hence
  all three welded conclusions, including the strictly positive transverse
  certificate.

This is what makes a genuine gauge reduction (redundant subgroup quotiented,
effective symmetry surviving and moving the coarse layer) carry the spine's
geometric certificate: there, the surviving symmetry moves the visible state by
design, so no nonconstant invariant class coordinate exists.
-/

namespace Integration.EquivariantChannel

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.StructuredObserver.ObserverBuild (readVec avg_readVec_ne_zero)

variable {G Rich Coarse Res K : Type} [Monoid G] {n : ℕ} [NeZero n]

/-! ## Charts: an action by bijections in coordinates -/

/-- An action by bijections on a carrier enumerated by `Fin n`.  This is the
data from which the permutation representation is built. -/
structure ActionChart (G Rich : Type) [Monoid G] (n : ℕ) where
  /-- The action. -/
  act : G → Rich → Rich
  /-- A pointwise inverse of each action map. -/
  actInv : G → Rich → Rich
  /-- Left inverse. -/
  actInv_left : ∀ g x, actInv g (act g x) = x
  /-- Right inverse. -/
  actInv_right : ∀ g x, act g (actInv g x) = x
  /-- The enumeration of the carrier. -/
  enum : Rich ≃ Fin n

namespace ActionChart

variable (C : ActionChart G Rich n)

/-- The permutation of coordinates induced by `g`; as in `ObserverBuild` it is
the inverse action that permutes coordinates. -/
def perm (g : G) : Equiv.Perm (Fin n) where
  toFun j := C.enum (C.actInv g (C.enum.symm j))
  invFun j := C.enum (C.act g (C.enum.symm j))
  left_inv j := by simp [C.actInv_right]
  right_inv j := by simp [C.actInv_left]

omit [NeZero n] in
@[simp] theorem perm_apply (g : G) (j : Fin n) :
    C.perm g j = C.enum (C.actInv g (C.enum.symm j)) := rfl

/-- The permutation representation on `ℝⁿ`: orthogonal, and fixing the constant
vector, so it respects the fixed/transverse splitting. -/
noncomputable def rep : FixedIsometryRep G n where
  act g x := WithLp.toLp 2 (fun j => x (C.perm g j))
  inner_map g x y := by
    rw [inner_eq_sum, inner_eq_sum]
    simpa using Equiv.sum_comp (C.perm g) (fun j => x j * y j)
  ones_fixed g := by ext j; simp
  map_sub g x y := by ext j; simp
  map_smul g c x := by ext j; simp

/-- The reading of a state: the constant vector plus its indicator. -/
theorem readVec_equivariant (g : G) (x : Rich) :
    readVec C.enum (C.act g x) = C.rep.act g (readVec C.enum x) := by
  ext j
  show 1 + (if j = C.enum (C.act g x) then (1 : ℝ) else 0)
      = 1 + (if C.perm g j = C.enum x then (1 : ℝ) else 0)
  have key : (j = C.enum (C.act g x)) ↔ (C.perm g j = C.enum x) := by
    constructor
    · rintro rfl
      simp [C.actInv_left]
    · intro hj
      have h1 : C.actInv g (C.enum.symm j) = x := C.enum.injective hj
      have h2 : C.enum.symm j = C.act g x := by rw [← h1, C.actInv_right]
      rw [← h2, Equiv.apply_symm_apply]
  exact congrArg _ (if_congr key rfl rfl)

end ActionChart

/-! ## Observers with a moving class coordinate -/

/-- Finite data for a symmetry-resolved observer whose transverse class
coordinate is **equivariant** rather than invariant: the symmetry permutes the
classes along a bijective action `actK`. -/
structure EqObserverBuild (G Rich Coarse Res K : Type) [Monoid G] where
  /-- The symmetry reduction. -/
  reduction : EquivariantQuotient G Rich Coarse
  /-- A pointwise inverse of each action map. -/
  actInv : G → Rich → Rich
  /-- Left inverse. -/
  actInv_left : ∀ g x, actInv g (reduction.actRich g x) = x
  /-- Right inverse. -/
  actInv_right : ∀ g x, reduction.actRich g (actInv g x) = x
  /-- The retained residual. -/
  residual : Rich → Res
  /-- The reassembly map. -/
  reopen : Coarse → Res → Rich
  /-- Reassembly is exact. -/
  reopen_project : ∀ x, reopen (reduction.proj x) (residual x) = x
  /-- The transverse class coordinate. -/
  cls : Rich → K
  /-- The induced action on classes. -/
  actK : G → K → K
  /-- Its pointwise inverse. -/
  actKInv : G → K → K
  /-- Left inverse. -/
  actKInv_left : ∀ g k, actKInv g (actK g k) = k
  /-- Right inverse. -/
  actKInv_right : ∀ g k, actK g (actKInv g k) = k
  /-- The class coordinate is equivariant. -/
  cls_equivariant : ∀ g x, cls (reduction.actRich g x) = actK g (cls x)
  /-- And nonconstant, so the channel is genuinely transverse. -/
  cls_separates : ∀ x, ∃ y, cls y ≠ cls x

namespace EqObserverBuild

variable [DecidableEq K] (B : EqObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)

/-- The chart underlying the build. -/
def chart : ActionChart G Rich n where
  act := B.reduction.actRich
  actInv := B.actInv
  actInv_left := B.actInv_left
  actInv_right := B.actInv_right
  enum := enum

omit [DecidableEq K] in
/-- The class coordinate transforms by the inverse action along `actInv`. -/
theorem cls_actInv (g : G) (x : Rich) : B.cls (B.actInv g x) = B.actKInv g (B.cls x) := by
  have h := B.cls_equivariant g (B.actInv g x)
  rw [B.actInv_right] at h
  rw [h, B.actKInv_left]

/-- The transverse channel: the indicator of the state's class. -/
noncomputable def channelVec (x : Rich) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if B.cls (enum.symm j) = B.cls x then (1 : ℝ) else 0)

/-- **The channel is equivariant even though the classes move.** -/
theorem channelVec_equivariant (g : G) (x : Rich) :
    channelVec B enum (B.reduction.actRich g x)
      = (B.chart enum).rep.act g (channelVec B enum x) := by
  ext j
  show (if B.cls (enum.symm j) = B.cls (B.reduction.actRich g x) then (1 : ℝ) else 0)
      = (if B.cls (enum.symm ((B.chart enum).perm g j)) = B.cls x then (1 : ℝ) else 0)
  have hsymm : enum.symm ((B.chart enum).perm g j) = B.actInv g (enum.symm j) := by
    simp [ActionChart.perm, chart]
  have key : (B.cls (enum.symm j) = B.cls (B.reduction.actRich g x))
      ↔ (B.cls (enum.symm ((B.chart enum).perm g j)) = B.cls x) := by
    rw [hsymm, B.cls_actInv, B.cls_equivariant]
    constructor
    · intro h; rw [h, B.actKInv_left]
    · intro h
      have := congrArg (B.actK g) h
      rwa [B.actKInv_right] at this
  exact if_congr key rfl rfl

theorem fluct_channelVec_ne_zero (x : Rich) : fluct (channelVec B enum x) ≠ 0 := by
  intro h
  obtain ⟨y, hy⟩ := B.cls_separates x
  have hc := (fluct_eq_zero_iff (channelVec B enum x)).mp h (enum x) (enum y)
  simp only [channelVec, lp_coord_apply, Equiv.symm_apply_apply] at hc
  simp [hy] at hc

/-- **The constructor.**  An equivariant (not necessarily invariant) class
coordinate suffices to build a symmetry-resolved observer, hence to inherit the
three welded conclusions. -/
noncomputable def toObserver : SymmetryResolvedObserver G Rich Coarse Res n where
  reduction := B.reduction
  residual := B.residual
  reopen := B.reopen
  reopen_project := B.reopen_project
  rep := (B.chart enum).rep
  read := readVec enum
  channel := channelVec B enum
  read_equivariant := fun g x => (B.chart enum).readVec_equivariant g x
  channel_equivariant := channelVec_equivariant B enum
  mean_ne_zero := avg_readVec_ne_zero enum
  fluct_ne_zero := fluct_channelVec_ne_zero B enum

@[simp] theorem toObserver_reduction : (B.toObserver enum).reduction = B.reduction := rfl

@[simp] theorem toObserver_read (x : Rich) : (B.toObserver enum).read x = readVec enum x := rfl

@[simp] theorem toObserver_channel (x : Rich) :
    (B.toObserver enum).channel x = channelVec B enum x := rfl

end EqObserverBuild

end Integration.EquivariantChannel
