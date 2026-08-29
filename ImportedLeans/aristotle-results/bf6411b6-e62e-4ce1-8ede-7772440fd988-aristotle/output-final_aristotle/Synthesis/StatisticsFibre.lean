import Synthesis.Vec15Fibre
import Synthesis.MoonshineBase
import AgdaMirror.Vec15Order

/-!
# Synthesis layer 2'''': the order/statistics layer lands in the mask geometry

`AgdaMirror.Vec15Order` develops an order and selection layer on the 15-lane
carrier: a concrete list view `toList15`, a threshold mask `selectMask15`, a
lane count `countMask15`, and the rank `rank15 = countMask15 ∘ selectMask15`.
Nothing there refers to the Monster base, the mask algebra, or the mask
geometry — the connection is only that both use fifteen slots.

Proved here: the connection is real and not merely numerical.

* `toList15_eq_ofFn` — the concrete list view is exactly the list transport of
  the fibre used by `Synthesis.MonsterFibre`, in the same prime order;
* `selectMask15_fibre` — the threshold mask is the mask `fun p => lane p ≤ t`
  over the prime base, i.e. an element of `MaskSSP`;
* `countMask15_eq_card`, `rank15_eq_card` — the lane count is the cardinality of
  the mask's support, so the rank counts the primes the mask keeps;
* `selectMask15_monotone` — the threshold family is a chain in the submask
  order, hence (`selectMask15_dvd`, via `maskProduct_dvd_iff`) a divisibility
  chain of mask products and (`selectMask15_dSSP_empty_mono`) a monotone path
  towards the collapse mask in the supplied ultrametric.

Boundary: `Vec15Order`'s statistical vocabulary (quartile, median, rank) is the
source material's naming for operations on a 15-tuple of naturals; no statistical
claim is made or used.
-/

namespace Synthesis.StatisticsFibre

open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.GodelLattice (Vec15)
open AgdaMirror.Vec15Order (PrimeCarrier15 toList15 selectMask15 countMask15 countBool rank15)
open Synthesis.MonsterFibre
open Synthesis.Vec15Fibre
open Synthesis.MoonshineBase

/-! ## The concrete list view is the fibre transport -/

/-- The order layer's list view is the list transport of the fibre, in the same
prime order. -/
theorem toList15_eq_ofFn (v : PrimeCarrier15) :
    toList15 v = List.ofFn (fun i : Fin 15 => vec15Equiv v (finToSsp i)) := by
  rfl

/-! ## The threshold mask is a Monster mask -/

/-- The threshold mask, read over the prime base. -/
def thresholdMask (t : Nat) (v : PrimeCarrier15) : MaskSSP :=
  vec15Equiv (selectMask15 t v)

/-- The threshold mask keeps exactly the primes whose lane is below the
threshold. -/
theorem selectMask15_fibre (t : Nat) (v : PrimeCarrier15) :
    thresholdMask t v = fun p => decide (vec15Equiv v p ≤ t) := by
  funext p; cases p <;> rfl

theorem countBool_eq (x : Bool) : countBool x = if x = true then 1 else 0 := by
  cases x <;> rfl

/-- The lane count is the cardinality of the mask's support. -/
theorem countMask15_eq_card (b : Vec15 Bool) :
    countMask15 b = (Finset.univ.filter (fun p : SSP => vec15Equiv b p = true)).card := by
  rw [Finset.card_filter, sum_over_base]
  cases b
  simp only [vec15Equiv_apply, vec15At, countMask15, countBool_eq]

/-- The rank counts the primes the threshold mask keeps. -/
theorem rank15_eq_card (t : Nat) (v : PrimeCarrier15) :
    rank15 t v = (Finset.univ.filter (fun p : SSP => thresholdMask t v p = true)).card :=
  countMask15_eq_card _

/-! ## The threshold family is a chain in the mask geometry -/

/-- Raising the threshold only adds primes: the threshold family is a chain in
the submask order. -/
theorem selectMask15_monotone {t t' : Nat} (h : t ≤ t') (v : PrimeCarrier15) (p : SSP) :
    thresholdMask t v p = true → thresholdMask t' v p = true := by
  rw [selectMask15_fibre, selectMask15_fibre]
  simp only [decide_eq_true_eq]
  intro hp
  exact hp.trans h

/-- Consequently the mask products form a divisibility chain. -/
theorem selectMask15_dvd {t t' : Nat} (h : t ≤ t') (v : PrimeCarrier15) :
    maskProduct (thresholdMask t v) ∣ maskProduct (thresholdMask t' v) :=
  (maskProduct_dvd_iff _ _).mpr (selectMask15_monotone h v)

/-- And the family moves monotonically towards the collapse mask in the supplied
ultrametric: a lower threshold is never further from the empty mask. -/
theorem selectMask15_dSSP_empty_mono {t t' : Nat} (h : t ≤ t') (v : PrimeCarrier15) :
    dSSP (thresholdMask t v) emptyMaskSSP ≤ dSSP (thresholdMask t' v) emptyMaskSSP :=
  dSSP_empty_mono (selectMask15_monotone h v)

end Synthesis.StatisticsFibre
