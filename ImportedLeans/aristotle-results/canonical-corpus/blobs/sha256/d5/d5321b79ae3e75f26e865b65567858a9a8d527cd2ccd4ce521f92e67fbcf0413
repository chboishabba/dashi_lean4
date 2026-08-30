import Integration.EquivariantChannel
import Spine.FiniteReindex

/-!
# The transverse certificate does not depend on how the carrier is listed

Every welded observer in this library is built from a finite carrier `Rich`
together with an **enumeration** `enum : Rich ≃ Fin n`: the reading of a state is
`ones + e_{enum x}` and the transverse channel is the indicator of its class,
both living in `EuclideanSpace ℝ (Fin n)`.  The nondegeneracy certificate is then
the anchored area `area2 (read x) (fluct (channel x))`.

That construction chooses a listing of the carrier.  Before the number it
produces may be treated as an invariant of the *structure* rather than of a
*presentation* of it, one has to know that a different listing gives the same
number.  This file proves exactly that.

The reindexing calculus itself is *not* owned here: `Spine.FiniteReindex` owns
it, for an arbitrary carrier and an arbitrary additive weight, and this file is
one of its consumers (the others being finite weighted folds and the
deletion/fibre decomposition).  `permVec`, `inner_permVec`, `avg_permVec`,
`fluct_permVec`, `area2_permVec` and `det_gram_reindex` are re-exported from
there.  What is proved here is only the observer-specific step:
* `readVec_reindex`, `channelVec_reindex` — changing the enumeration reindexes
  the reading and the channel by one and the same permutation;
* `nondegeneracy_reindex` — **the headline**: for any two enumerations of the
  same carrier, the welded observers built from them assign every state the same
  certificate.  So `nondegeneracy` is a function of the structured carrier and
  the class coordinate, not of the chosen listing.
* `certificate_presentation_independent` — the same statement packaged for the
  gauge lane, together with positivity and symmetry invariance, so that the
  three properties the certificate is used for are simultaneously
  presentation-free.

Nothing here is specific to a domain: the statements are about
`EuclideanSpace ℝ (Fin n)` and the generic observer constructors.
-/

namespace Integration.EnumInvariance

open RealInnerProductSpace
open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.StructuredObserver.ObserverBuild (readVec)
open Integration.EquivariantChannel
open Spine.FiniteReindex

variable {n : ℕ} [NeZero n]

/-! ## Reindexing coordinate vectors

Owned by `Spine.FiniteReindex`; re-exported here so that the statements below
read the same as before, but there is only one proof of each.
-/

export Spine.FiniteReindex (permVec permVec_apply inner_permVec norm_sq_permVec
  avg_permVec meanPart_permVec fluct_permVec area2_permVec gram_comp_perm
  det_gram_reindex)

/-! ## Changing the enumeration -/

variable {G Rich Coarse Res K : Type} [Monoid G]

/-- The permutation of coordinates relating two enumerations of the same
carrier. -/
def reindex (e₁ e₂ : Rich ≃ Fin n) : Equiv.Perm (Fin n) := e₂.symm.trans e₁

omit [NeZero n] in
@[simp] theorem reindex_apply (e₁ e₂ : Rich ≃ Fin n) (j : Fin n) :
    reindex e₁ e₂ j = e₁ (e₂.symm j) := rfl

omit [NeZero n] in
/-- Changing the enumeration reindexes the reading. -/
theorem readVec_reindex (e₁ e₂ : Rich ≃ Fin n) (x : Rich) :
    readVec e₂ x = permVec (reindex e₁ e₂) (readVec e₁ x) := by
  ext j
  show 1 + (if j = e₂ x then (1 : ℝ) else 0) = 1 + (if e₁ (e₂.symm j) = e₁ x then (1 : ℝ) else 0)
  have key : (j = e₂ x) ↔ (e₁ (e₂.symm j) = e₁ x) := by
    constructor
    · rintro rfl; simp
    · intro h
      have : e₂.symm j = x := e₁.injective h
      rw [← this, Equiv.apply_symm_apply]
  exact congrArg _ (if_congr key rfl rfl)

variable [DecidableEq K]

omit [NeZero n] in
/-- Changing the enumeration reindexes the transverse channel by the *same*
permutation. -/
theorem channelVec_reindex (B : EqObserverBuild G Rich Coarse Res K)
    (e₁ e₂ : Rich ≃ Fin n) (x : Rich) :
    EqObserverBuild.channelVec B e₂ x
      = permVec (reindex e₁ e₂) (EqObserverBuild.channelVec B e₁ x) := by
  ext j
  show (if B.cls (e₂.symm j) = B.cls x then (1 : ℝ) else 0)
      = (if B.cls (e₁.symm (e₁ (e₂.symm j))) = B.cls x then (1 : ℝ) else 0)
  rw [Equiv.symm_apply_apply]

/-- **The certificate is presentation independent.**  Two enumerations of the
same carrier give welded observers with the same nondegeneracy certificate at
every state. -/
theorem nondegeneracy_reindex (B : EqObserverBuild G Rich Coarse Res K)
    (e₁ e₂ : Rich ≃ Fin n) (x : Rich) :
    (B.toObserver e₂).nondegeneracy x = (B.toObserver e₁).nondegeneracy x := by
  show area2 (readVec e₂ x) (fluct (EqObserverBuild.channelVec B e₂ x))
      = area2 (readVec e₁ x) (fluct (EqObserverBuild.channelVec B e₁ x))
  rw [readVec_reindex e₁ e₂, channelVec_reindex B e₁ e₂, fluct_permVec, area2_permVec]

omit [NeZero n] in
/-- The same statement for the invariant-class constructor `ObserverBuild`. -/
theorem channelVec_reindex' (B : ObserverBuild G Rich Coarse Res K)
    (e₁ e₂ : Rich ≃ Fin n) (x : Rich) :
    ObserverBuild.channelVec B e₂ x
      = permVec (reindex e₁ e₂) (ObserverBuild.channelVec B e₁ x) := by
  ext j
  show (if B.cls (e₂.symm j) = B.cls x then (1 : ℝ) else 0)
      = (if B.cls (e₁.symm (e₁ (e₂.symm j))) = B.cls x then (1 : ℝ) else 0)
  rw [Equiv.symm_apply_apply]

theorem nondegeneracy_reindex' (B : ObserverBuild G Rich Coarse Res K)
    (e₁ e₂ : Rich ≃ Fin n) (x : Rich) :
    (B.toObserver e₂).nondegeneracy x = (B.toObserver e₁).nondegeneracy x := by
  show area2 (readVec e₂ x) (fluct (ObserverBuild.channelVec B e₂ x))
      = area2 (readVec e₁ x) (fluct (ObserverBuild.channelVec B e₁ x))
  rw [readVec_reindex e₁ e₂, channelVec_reindex' B e₁ e₂, fluct_permVec, area2_permVec]

/-- **The three properties of the certificate, all presentation free.**  For any
two listings of the carrier the certificate is the same number; it is strictly
positive; and it is constant along the symmetry.  So the welded certificate is
an invariant of the structured carrier together with its class coordinate. -/
theorem certificate_presentation_independent (B : EqObserverBuild G Rich Coarse Res K)
    (e₁ e₂ : Rich ≃ Fin n) :
    (∀ x, (B.toObserver e₂).nondegeneracy x = (B.toObserver e₁).nondegeneracy x) ∧
      (∀ x, 0 < (B.toObserver e₁).nondegeneracy x) ∧
      (∀ g x, (B.toObserver e₁).nondegeneracy (B.reduction.actRich g x)
        = (B.toObserver e₁).nondegeneracy x) :=
  ⟨nondegeneracy_reindex B e₁ e₂,
    (B.toObserver e₁).nondegeneracy_pos,
    (B.toObserver e₁).nondegeneracy_invariant⟩

/-! ## The family version

`Spine.FiniteReindex.det_gram_reindex` (re-exported above) is the underlying
linear-algebra fact in the form the family version needs: permuting a family of
vectors conjugates its Gram matrix by a permutation matrix and therefore leaves
the Gram determinant unchanged.
-/

end Integration.EnumInvariance
