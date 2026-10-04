import Mathlib.Tactic
import NSBControl.Rational345Round71PhysicalCarrier

/-!
# Round71 literal Galerkin reality closure

The ambient Lean radius-four field is useful for analytic estimates, while the
Agda Round71 carrier stores only one member of every `{k,-k}` orbit.  This file
proves the missing same-object fact: the literal Leray-projected Galerkin field
commutes with Fourier reality.

Consequently the ambient field is tangent to the canonical reality subspace;
we do not need a second Navier--Stokes operator for the structural carrier.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345Round71RealityField

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71PhysicalCarrier

/-- Mode negation as a finite permutation, used to reindex the convolution. -/
def negateModeEquiv : Mode ≃ Mode where
  toFun := negateMode
  invFun := negateMode
  left_inv := negateMode_involutive
  right_inv := negateMode_involutive

@[simp] theorem isZeroMode_negate_iff (k : Mode) :
    isZeroMode (negateMode k) ↔ isZeroMode k := by
  constructor
  · intro h j
    have hj := h j
    rw [kInt_negate] at hj
    omega
  · intro h j
    rw [kInt_negate]
    have hj := h j
    omega

@[simp] theorem normSq_negate (k : Mode) :
    normSq (negateMode k) = normSq k := by
  unfold normSq kReal
  simp [kInt_negate]

@[simp] theorem kComplex_negate (k : Mode) :
    kComplex (negateMode k) = - kComplex k := by
  funext j
  simp [kComplex, kReal, kInt_negate]

@[simp] theorem vecConj_involutive (v : Vec3) :
    vecConj (vecConj v) = v := by
  funext j
  simp [vecConj]

@[simp] theorem vecConj_add (u v : Vec3) :
    vecConj (u + v) = vecConj u + vecConj v := by
  funext j
  simp [vecConj]

@[simp] theorem vecConj_neg (v : Vec3) :
    vecConj (-v) = -vecConj v := by
  funext j
  simp [vecConj]

@[simp] theorem vecConj_smul (c : ℂ) (v : Vec3) :
    vecConj (c • v) = star c • vecConj v := by
  funext j
  simp [vecConj]

/-- The real Fourier wave-vector pairing picks up exactly one minus sign under
simultaneous mode-negation / velocity-conjugation. -/
theorem bilinearDot_mode_neg_conj (k : Mode) (v : Vec3) :
    bilinearDot (kComplex (negateMode k)) (vecConj v) =
      - star (bilinearDot (kComplex k) v) := by
  simp only [kComplex_negate]
  simp [bilinearDot, vecConj]

/-- Literal Leray projection respects Fourier reality. -/
theorem leray_reality (k : Mode) (v : Vec3) :
    leray (negateMode k) (vecConj v) = vecConj (leray k v) := by
  by_cases hz : isZeroMode k
  · have hnz : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hz
    simp [leray, hz, hnz, vecConj]
  · have hnz : ¬ isZeroMode (negateMode k) := by
      simpa using hz
    funext j
    simp only [leray, hz, hnz, dif_false]
    rw [normSq_negate, kComplex_negate]
    simp [bilinearDot, kComplex, kReal, kInt_negate, vecConj]
    ring

/-- Resonance is invariant under simultaneous negation of all three legs. -/
theorem resonates_negate_iff (p q k : Mode) :
    Resonates (negateMode p) (negateMode q) (negateMode k) ↔
      Resonates p q k := by
  constructor <;> intro h j
  · have hj := h j
    simp only [kInt_negate] at hj
    omega
  · have hj := h j
    simp only [kInt_negate]
    omega

/-- One ordered quadratic Navier--Stokes cell respects Fourier reality. -/
theorem projectedOrdered_decode_reality
    (a : CanonicalState) (p q k : Mode) :
    projectedOrderedBilinear (decode a) (decode a)
      (negateMode p) (negateMode q) (negateMode k) =
    vecConj (projectedOrderedBilinear (decode a) (decode a) p q k) := by
  by_cases hres : Resonates p q k
  · have hresNeg : Resonates (negateMode p) (negateMode q) (negateMode k) :=
      (resonates_negate_iff p q k).2 hres
    simp only [projectedOrderedBilinear, hres, hresNeg, if_true]
    rw [decode_reality a p, decode_reality a q]
    funext j
    rw [leray_reality]
    simp [bilinearDot, kComplex, kReal, kInt_negate, vecConj]
    ring
  · have hresNeg : ¬ Resonates (negateMode p) (negateMode q) (negateMode k) := by
      intro h
      exact hres ((resonates_negate_iff p q k).1 h)
    simp [projectedOrderedBilinear, hres, hresNeg, vecConj]

/-- Negation reindexes the whole finite convolution without changing its sum. -/
theorem doubleSum_negate_reindex
    (f : Mode → Mode → Vec3) :
    (∑ p : Mode, ∑ q : Mode, f p q) =
      ∑ p : Mode, ∑ q : Mode, f (negateMode p) (negateMode q) := by
  calc
    (∑ p : Mode, ∑ q : Mode, f p q)
        = ∑ p : Mode, ∑ q : Mode, f (negateMode p) q := by
          symm
          exact Equiv.sum_comp negateModeEquiv (fun p => ∑ q : Mode, f p q)
    _ = ∑ p : Mode, ∑ q : Mode, f (negateMode p) (negateMode q) := by
          apply Fintype.sum_congr
          intro p
          symm
          exact Equiv.sum_comp negateModeEquiv
            (fun q => f (negateMode p) q)

/-- The full literal projected nonlinearity of a decoded canonical state has
exact Fourier reality. -/
theorem projectedNonlinearity_decode_reality
    (a : CanonicalState) (k : Mode) :
    projectedNonlinearity (decode a) (negateMode k) =
      vecConj (projectedNonlinearity (decode a) k) := by
  unfold projectedNonlinearity projectedBilinear
  by_cases hz : isZeroMode k
  · have hnz : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hz
    simp [hz, hnz, vecConj]
  · have hnz : ¬ isZeroMode (negateMode k) := by simpa using hz
    simp only [hz, hnz, if_false]
    rw [doubleSum_negate_reindex
      (fun p q => projectedOrderedBilinear (decode a) (decode a) p q
        (negateMode k))]
    simp_rw [negateMode_involutive]
    simp_rw [projectedOrdered_decode_reality a]
    funext j
    simp [vecConj]

/-- The viscous linear part has exact Fourier reality. -/
theorem viscousLinear_decode_reality
    (a : CanonicalState) (k : Mode) :
    viscousLinear (decode a) (negateMode k) =
      vecConj (viscousLinear (decode a) k) := by
  by_cases hz : isZeroMode k
  · have hnz : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hz
    simp [viscousLinear, hz, hnz, vecConj]
  · have hnz : ¬ isZeroMode (negateMode k) := by simpa using hz
    rw [decode_reality a k]
    funext j
    simp [viscousLinear, hz, hnz, normSq_negate, vecConj]

/-- Main Round71 carrier theorem on structurally decoded states. -/
theorem galerkinField_decode_reality
    (a : CanonicalState) (k : Mode) :
    galerkinField (decode a) (negateMode k) =
      vecConj (galerkinField (decode a) k) := by
  rw [galerkinField_eq_linear_add_bilinear,
      galerkinField_eq_linear_add_bilinear]
  change
    viscousLinear (decode a) (negateMode k) +
      projectedNonlinearity (decode a) (negateMode k) =
    vecConj
      (viscousLinear (decode a) k + projectedNonlinearity (decode a) k)
  rw [viscousLinear_decode_reality a k,
      projectedNonlinearity_decode_reality a k,
      vecConj_add]

------------------------------------------------------------------------
-- Global reality involution and equivariance for arbitrary ambient states.
------------------------------------------------------------------------

/-- Fourier reality involution on the ambient radius-four state space. -/
def realityTransform (u : State) : State := fun k =>
  vecConj (u (negateMode k))

@[simp] theorem realityTransform_apply (u : State) (k : Mode) :
    realityTransform u k = vecConj (u (negateMode k)) := rfl

@[simp] theorem realityTransform_involutive (u : State) :
    realityTransform (realityTransform u) = u := by
  funext k
  simp [realityTransform]

/-- One ordered cell intertwines the global reality involution. -/
theorem projectedOrdered_realityTransform
    (left right : State) (p q k : Mode) :
    projectedOrderedBilinear (realityTransform left) (realityTransform right) p q k =
      vecConj
        (projectedOrderedBilinear left right
          (negateMode p) (negateMode q) (negateMode k)) := by
  by_cases hres : Resonates p q k
  · have hresNeg : Resonates (negateMode p) (negateMode q) (negateMode k) :=
      (resonates_negate_iff p q k).2 hres
    simp only [projectedOrderedBilinear, hres, hresNeg, if_true,
      realityTransform_apply]
    funext j
    rw [← leray_reality (negateMode k)]
    simp [bilinearDot, kComplex, kReal, kInt_negate, vecConj]
    ring
  · have hresNeg : ¬ Resonates (negateMode p) (negateMode q) (negateMode k) := by
      intro h
      exact hres ((resonates_negate_iff p q k).1 h)
    simp [projectedOrderedBilinear, hres, hresNeg, realityTransform, vecConj]

/-- The full quadratic convolution intertwines the reality involution. -/
theorem projectedNonlinearity_reality_equivariant
    (u : State) (k : Mode) :
    projectedNonlinearity (realityTransform u) k =
      realityTransform (projectedNonlinearity u) k := by
  unfold projectedNonlinearity projectedBilinear
  by_cases hz : isZeroMode k
  · have hnz : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hz
    simp [hz, hnz, realityTransform, vecConj]
  · have hnz : ¬ isZeroMode (negateMode k) := by simpa using hz
    simp only [hz, if_false, realityTransform_apply]
    rw [doubleSum_negate_reindex
      (fun p q => projectedOrderedBilinear (realityTransform u)
        (realityTransform u) p q k)]
    simp_rw [projectedOrdered_realityTransform u u]
    simp_rw [negateMode_involutive]
    funext j
    simp [projectedNonlinearity, projectedBilinear, hnz, vecConj]

/-- The viscous term intertwines the reality involution. -/
theorem viscousLinear_reality_equivariant (u : State) (k : Mode) :
    viscousLinear (realityTransform u) k =
      realityTransform (viscousLinear u) k := by
  by_cases hz : isZeroMode k
  · have hnz : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hz
    simp [viscousLinear, hz, hnz, realityTransform, vecConj]
  · have hnz : ¬ isZeroMode (negateMode k) := by simpa using hz
    funext j
    simp [viscousLinear, hz, hnz, realityTransform, normSq_negate, vecConj]

/-- Global symmetry theorem used with ODE uniqueness: the literal radius-four
Galerkin vector field commutes with Fourier reality on the entire ambient
finite state space. -/
theorem galerkinField_reality_equivariant (u : State) :
    galerkinField (realityTransform u) =
      realityTransform (galerkinField u) := by
  funext k
  rw [galerkinField_eq_linear_add_bilinear,
      galerkinField_eq_linear_add_bilinear]
  change
    viscousLinear (realityTransform u) k +
      projectedNonlinearity (realityTransform u) k =
    realityTransform
      (viscousLinear u + projectedNonlinearity u) k
  rw [viscousLinear_reality_equivariant,
      projectedNonlinearity_reality_equivariant]
  simp [realityTransform]

/-- No separate operator-level reality-preservation hypothesis remains. -/
def round71LiteralGalerkinRealityClosed : Bool := true

/-- Global equivariance needed for uniqueness-based trajectory invariance. -/
def round71GlobalRealityEquivarianceClosed : Bool := true

end Rational345Round71RealityField
end NSBControl
