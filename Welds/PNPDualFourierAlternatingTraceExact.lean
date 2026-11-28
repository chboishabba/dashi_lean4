import Mathlib
import Welds.PNPF3CollectiveNormalExact

open scoped BigOperators

namespace PNPDualFourier

-- Finite bilinear orthogonality transport. The phase signs and the
-- normalizer are explicit; the orthogonality premise is supplied by the
-- concrete product-F3 character identity, not by a small-tail assumption.
theorem join_sum {Y S T R : Type*} [Fintype Y] [Fintype S] [Fintype T]
    [CommRing R] (L : S → R) (K : T → R)
    (p : Y → S → R) (q : Y → T → R) (N : R)
    (compatible : S → T → Bool)
    (orth : ∀ s t, (∑ y, p y s * q y t) =
      if compatible s t then N else 0) :
    (∑ y, (∑ s, L s * p y s) * (∑ t, K t * q y t)) =
      N * ∑ s, ∑ t, if compatible s t then L s * K t else 0 := by
  classical
  calc
    _ = ∑ y, ∑ s, ∑ t, (L s * K t) * (p y s * q y t) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ s, ∑ t, ∑ y, (L s * K t) * (p y s * q y t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ s, ∑ t, N * (if compatible s t then L s * K t else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum, orth]
      cases h : compatible s t <;> simp [h, mul_comm]
    _ = _ := by simp only [Finset.mul_sum]

-- Squared omitted-energy certificate after subtraction of the exact
-- retained energies. Here a and b are nonnegative amplitude envelopes.
theorem omitted_energy_bound {ι : Type*} (O : Finset ι)
    (a b : ι → ℚ) (EL ER : ℚ)
    (hL : (∑ i ∈ O, a i^2) ≤ EL)
    (hR : (∑ i ∈ O, b i^2) ≤ ER) :
    (∑ i ∈ O, a i*b i)^2 ≤ EL*ER := by
  have na : 0 ≤ ∑ i ∈ O, a i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have nb : 0 ≤ ∑ i ∈ O, b i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact (PNPSignedCharacterTail.tail_squared O a b).trans
    (mul_le_mul hL hR nb (na.trans hL))

end PNPDualFourier

namespace PNPAlternatingState

-- The schedule is fixed, each handoff carries ONLY S, the terminal
-- observer sees only S. No timing, external memory or random access.
def stateAt {A S : Type*} (schedule : Nat → Bool) (step : Nat → Bool → A → S → S)
    (init : S) (x y : A) : Nat → S
  | 0 => init
  | t+1 => if schedule t then step t true x (stateAt schedule step init x y t)
    else step t false y (stateAt schedule step init x y t)

-- Rectangle closure proved on the literal alternating state trace,
-- rather than assuming an arbitrary mixed-input circuit is rectangular.
theorem mix {A S : Type*} (schedule : Nat → Bool) (step : Nat → Bool → A → S → S)
    (init : S) (x y : A) (k : Nat)
    (h : ∀ i ≤ k, stateAt schedule step init x x i = stateAt schedule step init y y i) :
    ∀ i ≤ k, stateAt schedule step init x y i = stateAt schedule step init x x i := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    have hlt : i ≤ k := by omega
    have hm := ih hlt
    have hp := h i hlt
    cases hs : schedule i with
    | true => simp [stateAt,hs,hm]
    | false =>
      have hd := h (i+1) hi
      simp only [stateAt,hs,Bool.false_eq_true,if_false] at hd ⊢
      rw [hm,hp]
      simpa only [hp] using hd.symm

theorem transcript_injective {A S : Type*} (schedule : Nat → Bool)
    (step : Nat → Bool → A → S → S) (init : S) (k : Nat) (accept : S → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y k) = true ↔ x=y) :
    Function.Injective (fun x : A => fun i : Fin (k+1) => stateAt schedule step init x x i.val) := by
  intro x y eq
  have h : ∀ i ≤ k, stateAt schedule step init x x i = stateAt schedule step init y y i := by
    intro i hi
    exact congrFun eq ⟨i,by omega⟩
  have hm := mix schedule step init x y k h k (Nat.le_refl k)
  apply (sound x y).mp
  rw [hm]
  exact (sound x x).mpr rfl

theorem handoff_cardinality {A S : Type*} [Fintype A] [Fintype S]
    (schedule : Nat → Bool) (step : Nat → Bool → A → S → S) (init : S)
    (k : Nat) (accept : S → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y k) = true ↔ x=y) :
    Fintype.card A ≤ (Fintype.card S)^(k+1) := by
  classical
  simpa using Fintype.card_le_of_injective _ (transcript_injective schedule step init k accept sound)

-- Finite Boolean storage, fixed public schedule. This is a handoff
-- information bound, not a superpolynomial lower bound on arbitrary RAM.
theorem bit_handoff_bound (n s : Nat) (schedule : Nat → Bool)
    (step : Nat → Bool → (Fin n → Bool) → (Fin s → Bool) → (Fin s → Bool))
    (init : Fin s → Bool) (k : Nat) (accept : (Fin s → Bool) → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y k) = true ↔ x=y) :
    2^n ≤ (2^s)^(k+1) := by
  simpa using handoff_cardinality schedule step init k accept sound

end PNPAlternatingState

namespace PNPGuardedTranslation

-- Predicate used by the online search. Prefix closure is unconditional
-- for a fixed already compiled period; it says nothing about discovery.
def repeatOK {ι : Type*} (v D G : ι → ℤ)
    (higher : List (ι → ℤ)) (k : Nat) : Prop :=
  ∀ j : Nat, j < k →
    (∀ i, G i ≤ v i + (j:ℤ)*D i) ∧
    (∀ h ∈ higher, ¬ ∀ i, h i ≤ v i + (j:ℤ)*D i)

theorem repeat_prefix {ι : Type*} (v D G : ι → ℤ)
    (higher : List (ι → ℤ)) {k l : Nat} (h : repeatOK v D G higher k)
    (hle : l ≤ k) : repeatOK v D G higher l :=
  fun j hj => h j (lt_of_lt_of_le hj hle)

theorem selected_extrema (v D g : ℤ) (k : Nat) (hk : 0 < k) :
    (∀ j : Nat, j < k → g ≤ v+(j:ℤ)*D) ↔
    g ≤ v+min 0 (((k-1:Nat):ℤ)*D) := by
  by_cases hD : 0 ≤ D
  · rw [min_eq_left (mul_nonneg (Int.natCast_nonneg _) hD)]
    constructor
    · intro h
      simpa using h 0 hk
    · intro h j hj
      have hn := mul_nonneg (Int.natCast_nonneg j) hD
      linarith
  · have hD' : D ≤ 0 := le_of_lt (lt_of_not_ge hD)
    rw [min_eq_right (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hD')]
    constructor
    · intro h
      exact h (k-1) (by omega)
    · intro h j hj
      have hle : (j:ℤ) ≤ ((k-1:Nat):ℤ) := by exact_mod_cast (show j ≤ k-1 by omega)
      have hm := mul_le_mul_of_nonpos_right hle hD'
      linarith

end PNPGuardedTranslation
