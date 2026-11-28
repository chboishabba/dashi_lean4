import Mathlib
import Welds.PNPStackEmittedListExact
import Welds.PNPMaterializedValuationResourceExact

namespace PNPPrimeValuationPriority
open scoped BigOperators

abbrev Valuation := ℕ →₀ ℕ

def PrimeSupported (v : Valuation) : Prop :=
  ∀ p ∈ v.support, Nat.Prime p

def pack (v : Valuation) : Nat := v.prod (· ^ ·)

theorem pack_nonzero (v : Valuation) (hv : PrimeSupported v) : pack v ≠ 0 := by
  unfold pack Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hv p hp).ne_zero)

-- The actual integer factorization is exactly the stored sparse vector.
-- No numeric digit or prime-factor oracle is assumed in this equality.
theorem factorization_pack (v : Valuation) (hv : PrimeSupported v) :
    (pack v).factorization = v :=
  Nat.factorization_prod_pow_eq_self hv

theorem guard_iff_dvd (take v : Valuation)
    (ht : PrimeSupported take) (hv : PrimeSupported v) :
    take ≤ v ↔ pack take ∣ pack v := by
  simpa only [factorization_pack take ht, factorization_pack v hv] using
    (Nat.factorization_le_iff_dvd (pack_nonzero take ht) (pack_nonzero v hv))

theorem supported_add (a b : Valuation) (ha : PrimeSupported a)
    (hb : PrimeSupported b) : PrimeSupported (a+b) := by
  intro p hp
  by_contra h
  have az : a p = 0 := by
    by_contra ne
    exact h (ha p (Finsupp.mem_support_iff.mpr ne))
  have bz : b p = 0 := by
    by_contra ne
    exact h (hb p (Finsupp.mem_support_iff.mpr ne))
  exact (Finsupp.mem_support_iff.mp hp) (by simp [az,bz])

theorem pack_add (a b : Valuation) (ha : PrimeSupported a)
    (hb : PrimeSupported b) : pack (a+b) = pack a * pack b := by
  have hn := pack_nonzero (a+b) (supported_add a b ha hb)
  have hm := mul_ne_zero (pack_nonzero a ha) (pack_nonzero b hb)
  have hf : (pack (a+b)).factorization = (pack a * pack b).factorization := by
    rw [factorization_pack _ (supported_add a b ha hb),
        Nat.factorization_mul (pack_nonzero a ha) (pack_nonzero b hb),
        factorization_pack a ha, factorization_pack b hb]
  calc
    pack (a+b) = (pack (a+b)).factorization.prod (· ^ ·) :=
      (Nat.prod_factorization_pow_eq_self hn).symm
    _ = (pack a * pack b).factorization.prod (· ^ ·) := by rw [hf]
    _ = pack a * pack b := Nat.prod_factorization_pow_eq_self hm

-- Exact numeric transition for an enabled guard with residual exponents.
-- Multiplying by the denominator gives the intended integer successor;
-- this also covers cancellation provided the guarded take is the actual
-- reduced denominator (the emitter still owes noncancellation).
theorem transition_product (take give rest : Valuation)
    (ht : PrimeSupported take) (hg : PrimeSupported give) (hr : PrimeSupported rest) :
    pack take * pack (give+rest) = pack (take+rest) * pack give := by
  rw [pack_add give rest hg hr,pack_add take rest ht hr]
  ac_rfl

structure Edge where
  take : Valuation
  give : Valuation
  takePrime : PrimeSupported take
  givePrime : PrimeSupported give

noncomputable def firstSparse (v : Valuation) : List Edge → Option Edge
  | [] => none
  | e::es => if e.take ≤ v then some e else firstSparse v es

noncomputable def firstLiteral (n : Nat) : List Edge → Option Edge
  | [] => none
  | e::es => if pack e.take ∣ n then some e else firstLiteral n es

-- First applicable edge, not just existence of an enabled edge.
theorem first_exact (v : Valuation) (hv : PrimeSupported v) (P : List Edge) :
    firstSparse v P = firstLiteral (pack v) P := by
  induction P with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.take ≤ v
    · have hd := (guard_iff_dvd e.take v e.takePrime hv).mp h
      simp [firstSparse,firstLiteral,h,hd]
    · have hd : ¬ pack e.take ∣ pack v :=
        fun h' => h ((guard_iff_dvd e.take v e.takePrime hv).mpr h')
      simp [firstSparse,firstLiteral,h,hd,ih]

-- The existing emitted five-lane edge is the source owner. The bridge
-- requires the actual injective prime allocation for the five lanes and
-- phase tags. No supplied guard equivalence is silently marked proven.
theorem emitted_guard (r : PNPStackEmittedList.Edge) (s : PNPStackEmittedList.State)
    (e : Edge) (v : Valuation) (hv : PrimeSupported v)
    (layoutExact : PNPStackEmittedList.enabled r s ↔ e.take ≤ v) :
    PNPStackEmittedList.enabled r s ↔ pack e.take ∣ pack v :=
  layoutExact.trans (guard_iff_dvd e.take v e.takePrime hv)

end PNPPrimeValuationPriority
