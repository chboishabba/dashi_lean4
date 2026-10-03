import Mathlib.Tactic
import NSBControl.Rational345Round71RealityField
import NSBControl.Rational345Round71TransverseField

/-!
# Round71 canonical nonlinear conservation on the real radius-four carrier

Agda `rawProjectedPairing` is the finite sum

  Σ_k Re ⟪u_k, projectedNonlinearity(u)_k⟫.

For a Fourier-real divergence-free state this vanishes exactly.  The proof
uses the literal Lean convolution and the same finite reindexing behind the
standard transport-energy cancellation:

  (k,p,q) ↦ (-q,p,-k).

For a resonant cell `p+q=k`, divergence freedom gives
`u_p·(-k) = -u_p·q`; Fourier reality identifies the paired Hermitian factor;
hence the two real powers are negatives.  The map is an involution of the
complete finite radius-four incidence cube, so the total sum is zero.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345Round71NonlinearConservation

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71PhysicalCarrier
open Rational345Round71RealityField
open Rational345Round71TransverseField

/-- Real counterpart of Agda R39/R648 `rawProjectedPairing`.  The zero mode may
be included because its literal projected nonlinearity is zero. -/
def rawProjectedPairingReal (u : State) : ℝ :=
  ∑ k : Mode, (hermitianDot (u k) (projectedNonlinearity u k)).re

------------------------------------------------------------------------
-- Hermitian linearity and Leray removal against a transverse test vector.
------------------------------------------------------------------------

theorem hermitianDot_add_right (w u v : Vec3) :
    hermitianDot w (u + v) = hermitianDot w u + hermitianDot w v := by
  simp [hermitianDot, Finset.mul_sum]
  ring

theorem hermitianDot_sub_right (w u v : Vec3) :
    hermitianDot w (u - v) = hermitianDot w u - hermitianDot w v := by
  simp [hermitianDot, Finset.mul_sum]
  ring

theorem hermitianDot_smul_right (w : Vec3) (c : ℂ) (v : Vec3) :
    hermitianDot w (c • v) = c * hermitianDot w v := by
  simp [hermitianDot, Finset.mul_sum]
  ring

theorem hermitianDot_sum_right
    {ι : Type*} [Fintype ι] (w : Vec3) (f : ι → Vec3) :
    hermitianDot w (∑ i, f i) = ∑ i, hermitianDot w (f i) := by
  simp [hermitianDot, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem bilinearDot_comm (u v : Vec3) : bilinearDot u v = bilinearDot v u := by
  simp [bilinearDot]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Since the wave vector is real, pairing it in the Hermitian right slot is
the conjugate of the bilinear transversality scalar. -/
theorem hermitianDot_kComplex_right (u : Vec3) (k : Mode) :
    hermitianDot u (kComplex k) =
      star (bilinearDot (kComplex k) u) := by
  simp [hermitianDot, bilinearDot, kComplex, kReal]
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- Leray projection is invisible when tested against a transverse output
velocity. -/
theorem hermitianDot_leray_of_transverse
    {k : Mode} (hk : ¬ isZeroMode k)
    (u v : Vec3)
    (hu : bilinearDot (kComplex k) u = 0) :
    hermitianDot u (leray k v) = hermitianDot u v := by
  rw [leray_eq_sub_smul hk]
  rw [hermitianDot_sub_right, hermitianDot_smul_right,
      hermitianDot_kComplex_right, hu]
  simp

------------------------------------------------------------------------
-- Unprojected ordered cell and exact pairing with the literal R30 cell.
------------------------------------------------------------------------

/-- Scalar real power of one ordered resonant incidence after removing Leray
against a transverse test velocity. -/
def energyCell (u : State) (p q k : Mode) : ℝ :=
  if isZeroMode k then 0
  else if Resonates p q k then
    (-Complex.I * bilinearDot (u p) (kComplex q) *
      hermitianDot (u k) (u q)).re
  else 0

/-- Pairing with the actual projected ordered term equals the unprojected
energy cell for divergence-free states. -/
theorem projectedOrdered_power_eq_energyCell
    (u : State)
    (hdiv : ∀ m, bilinearDot (kComplex m) (u m) = 0)
    (p q k : Mode) :
    (hermitianDot (u k)
      (projectedOrderedBilinear u u p q k)).re = energyCell u p q k := by
  by_cases hk : isZeroMode k
  · simp [energyCell, hk, projectedOrderedBilinear, leray, hermitianDot]
  · by_cases hres : Resonates p q k
    · simp only [energyCell, hk, hres, if_false, if_true,
        projectedOrderedBilinear]
      let a : ℂ := bilinearDot (u p) (kComplex q)
      let v : Vec3 := fun j => a * u q j
      have hv : v = a • u q := by rfl
      have hproj :
          hermitianDot (u k) (leray k v) = hermitianDot (u k) v :=
        hermitianDot_leray_of_transverse hk (u k) v (hdiv k)
      have hterm :
          (fun j => -Complex.I * leray k v j) =
            (-Complex.I) • leray k v := by rfl
      rw [show (fun j => -Complex.I *
          leray k (fun a' => bilinearDot (u p) (kComplex q) * u q a') j)
          = (fun j => -Complex.I * leray k v j) by rfl]
      rw [hterm, hermitianDot_smul_right, hproj, hv,
          hermitianDot_smul_right]
      simp [a]
      ring
    · simp [energyCell, hk, hres, projectedOrderedBilinear, hermitianDot]

------------------------------------------------------------------------
-- Raw pairing equals the complete ordered-cell real-power fold.
------------------------------------------------------------------------

theorem rawProjectedPairingReal_eq_cellSum
    (u : State)
    (hdiv : ∀ m, bilinearDot (kComplex m) (u m) = 0) :
    rawProjectedPairingReal u =
      ∑ k : Mode, ∑ p : Mode, ∑ q : Mode, energyCell u p q k := by
  unfold rawProjectedPairingReal
  apply Finset.sum_congr rfl
  intro k hkMem
  by_cases hk : isZeroMode k
  · simp [projectedNonlinearity, projectedBilinear, hk, energyCell]
  · unfold projectedNonlinearity projectedBilinear
    simp only [hk, if_false]
    rw [hermitianDot_sum_right]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hermitianDot_sum_right]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact projectedOrdered_power_eq_energyCell u hdiv p q k

------------------------------------------------------------------------
-- The energy-leg involution and pairwise cancellation.
------------------------------------------------------------------------

/-- Reindex `(k,q)` by the energy partner `(-q,-k)` while leaving the advecting
leg `p` fixed. -/
def energyPairEquiv : (Mode × Mode) ≃ (Mode × Mode) where
  toFun := fun kq => (negateMode kq.2, negateMode kq.1)
  invFun := fun kq => (negateMode kq.2, negateMode kq.1)
  left_inv := by
    intro kq
    rcases kq with ⟨k,q⟩
    simp
  right_inv := by
    intro kq
    rcases kq with ⟨k,q⟩
    simp

/-- Resonance is exactly preserved by the energy-pair involution. -/
theorem resonates_energyPair_iff (p q k : Mode) :
    Resonates p (negateMode k) (negateMode q) ↔ Resonates p q k := by
  constructor <;> intro h j
  · have hj := h j
    simp only [kInt_negate] at hj
    have hpq : kInt p j + kInt q j = kInt k j := by omega
    exact hpq
  · have hj := h j
    simp only [kInt_negate]
    omega

/-- Resonance plus transversality converts the partner advection scalar. -/
theorem advectionScalar_energyPair
    (u : State)
    (hdiv : ∀ m, bilinearDot (kComplex m) (u m) = 0)
    {p q k : Mode} (hres : Resonates p q k) :
    bilinearDot (u p) (kComplex (negateMode k)) =
      - bilinearDot (u p) (kComplex q) := by
  have hkadd : kComplex k = kComplex p + kComplex q := by
    funext j
    simp [kComplex, kReal, ← hres j]
  have hpzero : bilinearDot (u p) (kComplex p) = 0 := by
    rw [bilinearDot_comm]
    exact hdiv p
  rw [kComplex_negate, hkadd]
  simp [bilinearDot, hpzero, Finset.mul_sum]
  ring

/-- The Hermitian factor of the partner cell is exactly the original factor
when Fourier reality is used. -/
theorem hermitian_energyPair
    (u : State)
    (hreality : ∀ m, u (negateMode m) = vecConj (u m))
    (q k : Mode) :
    hermitianDot (u (negateMode q)) (u (negateMode k)) =
      hermitianDot (u k) (u q) := by
  rw [hreality q, hreality k]
  simp [hermitianDot, vecConj]
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- Every cell is the negative of its energy-pair partner. -/
theorem energyCell_pair_cancel
    (u : State)
    (hreality : ∀ m, u (negateMode m) = vecConj (u m))
    (hdiv : ∀ m, bilinearDot (kComplex m) (u m) = 0)
    (p q k : Mode) :
    energyCell u p (negateMode k) (negateMode q) =
      - energyCell u p q k := by
  by_cases hk : isZeroMode k
  · by_cases hres : Resonates p q k
    · have hpair : Resonates p (negateMode k) (negateMode q) :=
        (resonates_energyPair_iff p q k).2 hres
      have hkn : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hk
      have hcoeff : bilinearDot (u p) (kComplex (negateMode k)) = 0 := by
        simp [hk, kComplex, kReal]
      simp [energyCell, hk, hpair, hcoeff]
    · have hpair : ¬ Resonates p (negateMode k) (negateMode q) := by
        exact fun h => hres ((resonates_energyPair_iff p q k).1 h)
      simp [energyCell, hk, hpair]
  · by_cases hq : isZeroMode q
    · have hqn : isZeroMode (negateMode q) := (isZeroMode_negate_iff q).2 hq
      have hqvec : kComplex q = 0 := by
        funext j
        have hj := hq j
        simp [kComplex, kReal, hj]
      simp [energyCell, hk, hq, hqn, hqvec, bilinearDot]
    · have hkPair : ¬ isZeroMode (negateMode q) := by simpa using hq
      by_cases hres : Resonates p q k
      · have hpair : Resonates p (negateMode k) (negateMode q) :=
          (resonates_energyPair_iff p q k).2 hres
        rw [energyCell, energyCell]
        simp only [hk, hkPair, hres, hpair, if_false, if_true]
        rw [advectionScalar_energyPair u hdiv hres,
            hermitian_energyPair u hreality q k]
        simp
        ring
      · have hpair : ¬ Resonates p (negateMode k) (negateMode q) := by
          exact fun h => hres ((resonates_energyPair_iff p q k).1 h)
        simp [energyCell, hk, hkPair, hres, hpair]

/-- For each advecting mode `p`, the complete `(k,q)` fold vanishes by the
involutive reindexing. -/
theorem energyCell_sum_kq_zero
    (u : State)
    (hreality : ∀ m, u (negateMode m) = vecConj (u m))
    (hdiv : ∀ m, bilinearDot (kComplex m) (u m) = 0)
    (p : Mode) :
    (∑ k : Mode, ∑ q : Mode, energyCell u p q k) = 0 := by
  have hreindex :
      (∑ kq : Mode × Mode, energyCell u p kq.2 kq.1) =
      ∑ kq : Mode × Mode,
        energyCell u p (negateMode kq.1) (negateMode kq.2) := by
    symm
    exact Equiv.sum_comp energyPairEquiv
      (fun kq : Mode × Mode => energyCell u p kq.2 kq.1)
  have hneg :
      (∑ kq : Mode × Mode,
        energyCell u p (negateMode kq.1) (negateMode kq.2)) =
      -(∑ kq : Mode × Mode, energyCell u p kq.2 kq.1) := by
    simp_rw [energyCell_pair_cancel u hreality hdiv]
    exact Finset.sum_neg_distrib
  have hzero :
      (∑ kq : Mode × Mode, energyCell u p kq.2 kq.1) = 0 := by
    linarith [hreindex.trans hneg]
  simpa [Fintype.sum_prod_type, Finset.sum_comm] using hzero

/-- Canonical nonlinear conservation on the real radius-four carrier. -/
theorem rawProjectedPairingReal_eq_zero
    (u : State)
    (hreality : ∀ k, u (negateMode k) = vecConj (u k))
    (hdiv : ∀ k, bilinearDot (kComplex k) (u k) = 0) :
    rawProjectedPairingReal u = 0 := by
  rw [rawProjectedPairingReal_eq_cellSum u hdiv]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p hp
  exact energyCell_sum_kq_zero u hreality hdiv p

/-- The third structural field of Agda `LivePhysicalPacketStructure` has a
literal real radius-four counterpart. -/
def round71CanonicalNonlinearConservationClosed : Bool := true

end Rational345Round71NonlinearConservation
end NSBControl
