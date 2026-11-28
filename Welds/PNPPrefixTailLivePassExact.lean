import Mathlib
import Welds.PNPQuadraticMobiusExact
import Welds.PNPDualFourierAlternatingTraceExact

namespace PNPPrefixTail

def survives (bad : Nat → Bool) (k : Nat) : Prop :=
  ∀ j < k, bad j = false

def removedAt (bad : Nat → Bool) (j : Nat) : Prop :=
  survives bad j ∧ bad j = true

theorem first_failure_unique {bad : Nat → Bool} {i j : Nat}
    (hi : removedAt bad i) (hj : removedAt bad j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have e := hj.1 i h
    rw [hi.2] at e
    contradiction
  · exact h
  · have e := hi.1 j h
    rw [hj.2] at e
    contradiction

theorem prefix_step (bad : Nat → Bool) (k : Nat) :
    survives bad (k+1) ↔ survives bad k ∧ bad k = false := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega),h k (by omega)⟩
  · rintro ⟨h,hk⟩ j hj
    by_cases e : j=k
    · simpa [e] using hk
    · exact h j (by omega)

theorem first_failure_exists (bad : Nat → Bool) (m : Nat)
    (h : ¬ survives bad m) : ∃ j < m, removedAt bad j := by
  induction m with
  | zero =>
    exfalso
    apply h
    intro j hj
    omega
  | succ m ih =>
    by_cases hp : survives bad m
    · refine ⟨m,by omega,hp,?_⟩
      cases hb : bad m with
      | true => rfl
      | false =>
        exact False.elim (h ((prefix_step bad m).mpr ⟨hp,hb⟩))
    · obtain ⟨j,hj,hr⟩ := ih hp
      exact ⟨j,by omega,hr⟩

-- The original prefix minus the final source is precisely the disjoint
-- union of first-failure events. No signed intersection is treated as
-- a disjoint source assignment set.
theorem removed_between (bad : Nat → Bool) (k m : Nat) (hkm : k ≤ m) :
    (survives bad k ∧ ¬ survives bad m) ↔
      ∃ j, k ≤ j ∧ j < m ∧ removedAt bad j := by
  constructor
  · rintro ⟨hk,hm⟩
    obtain ⟨j,hj,hr⟩ := first_failure_exists bad m hm
    have hkj : k ≤ j := by
      by_contra hn
      have e := hk j (by omega)
      rw [hr.2] at e
      contradiction
    exact ⟨j,hkj,hj,hr⟩
  · rintro ⟨j,hkj,hjm,hj⟩
    exact ⟨fun i hi => hj.1 i (by omega),
      fun h => by have e := h j hjm; rw [hj.2] at e; contradiction⟩

-- H is the exact prefix histogram; r0,r1,r2 are actual disjoint removed
-- label masses; c0,c1,c2 upper-bound those masses.
theorem directional (h0 h1 h2 r0 r1 r2 c0 c1 c2 : ℚ)
    (a0 : 0 ≤ r0) (a1 : 0 ≤ r1) (a2 : 0 ≤ r2)
    (b0 : r0 ≤ c0) (b1 : r1 ≤ c1) (b2 : r2 ≤ c2) :
    2*h0-h1-h2-2*c0 ≤ 2*(h0-r0)-(h1-r1)-(h2-r2) ∧
    2*(h0-r0)-(h1-r1)-(h2-r2) ≤ 2*h0-h1-h2+c1+c2 := by
  constructor <;> linarith

-- The old magnitude-only restriction bound is false, even for a
-- three-point cube fibre: (1,1,1) has zero character; (1,0,0) has norm 1.
theorem character_not_subset_monotone :
    PNPSignedCharacterTail.energy ⟨1,1,1⟩ = 0 ∧
    PNPSignedCharacterTail.energy ⟨1,0,0⟩ = 1 := by
  norm_num [PNPSignedCharacterTail.energy]

end PNPPrefixTail

namespace PNPAlternatingState

-- Omit the public initial state from the transcript; only actual
-- handoffs carry information. Each pass may have arbitrary internal
-- reuse, provided no other information crosses to the next pass.
theorem handoff_injective_no_initial {A S : Type*} (schedule : Nat → Bool)
    (step : Nat → Bool → A → S → S) (init : S) (k : Nat) (accept : S → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y k) = true ↔ x=y) :
    Function.Injective (fun x : A => fun i : Fin k => stateAt schedule step init x x (i.val+1)) := by
  intro x y eq
  have h : ∀ i ≤ k, stateAt schedule step init x x i = stateAt schedule step init y y i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrFun eq ⟨i,by omega⟩
  have hm := mix schedule step init x y k h k (Nat.le_refl k)
  apply (sound x y).mp
  rw [hm]
  exact (sound x x).mpr rfl

theorem handoff_no_initial {A S : Type*} [Fintype A] [Fintype S]
    (schedule : Nat → Bool) (step : Nat → Bool → A → S → S)
    (init : S) (k : Nat) (accept : S → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y k) = true ↔ x=y) :
    Fintype.card A ≤ (Fintype.card S)^k := by
  classical
  simpa using Fintype.card_le_of_injective _ (handoff_injective_no_initial schedule step init k accept sound)

theorem twoPow_lt (a b : Nat) (h : a<b) : (2:Nat)^a < 2^b := by
  have hp : 0 < (2:Nat)^a := pow_pos (by decide) _
  have hd : 0 < b-a := by omega
  have hq : 1 < (2:Nat)^(b-a) := by
    cases e : b-a with
    | zero => omega
    | succ d =>
      rw [pow_succ]
      have ht : 0 < (2:Nat)^d := pow_pos (by decide) _
      omega
  calc
    2^a < 2^a * 2^(b-a) := by
      simpa using Nat.mul_lt_mul_of_pos_left hq hp
    _ = 2^b := by rw [← pow_add, show a+(b-a)=b by omega]

-- k epochs with s framed bits crossing each handoff: n <= s*k.
-- No arbitrary random access, external scratchpad or hidden timing.
theorem bit_epoch_bound (n s k : Nat) (schedule : Nat → Bool)
    (step : Nat → Bool → (Fin n → Bool) → (Fin s → Bool) → (Fin s → Bool))
    (init : Fin s → Bool) (accept : (Fin s → Bool) → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y k) = true ↔ x=y) :
    n ≤ s*k := by
  have h : 2^n ≤ (2^s)^k := by
    simpa using handoff_no_initial schedule step init k accept sound
  rw [← pow_mul] at h
  by_contra hn
  exact (not_le_of_gt (twoPow_lt (s*k) n (by omega))) h

-- Lane count is not storage in bits. The bound requires fixed lane
-- identities and a bound b on each lane's encoded bit width.
theorem lane_pass_bound (n w b p : Nat) (schedule : Nat → Bool)
    (step : Nat → Bool → (Fin n → Bool) → (Fin w → Fin (2^b)) → (Fin w → Fin (2^b)))
    (init : Fin w → Fin (2^b)) (accept : (Fin w → Fin (2^b)) → Bool)
    (sound : ∀ x y, accept (stateAt schedule step init x y (2*p)) = true ↔ x=y) :
    n ≤ b*w*(2*p) := by
  have h : 2^n ≤ ((2^b)^w)^(2*p) := by
    simpa using handoff_no_initial schedule step init (2*p) accept sound
  simp only [← pow_mul] at h
  by_contra hn
  exact (not_le_of_gt (twoPow_lt (b*w*(2*p)) n (by omega))) h

end PNPAlternatingState


namespace PNPGuardedTranslation

-- For the actual two-repetition probe, only positive shifted guard
-- thresholds on nonnegative valuations can matter.
theorem guard_two_stable {ι : Type*} (v v' D G : ι → ℤ)
    (nn : ∀ i, 0 ≤ v i) (nn' : ∀ i, 0 ≤ v' i)
    (same : ∀ i, 0 < G i-min 0 (D i) → v i=v' i)
    (j : Nat) (hj : j<2) :
    (∀ i, G i ≤ v i+(j:ℤ)*D i) ↔
    (∀ i, G i ≤ v' i+(j:ℤ)*D i) := by
  have trivialGuard : ∀ i, ¬ 0 < G i-min 0 (D i) →
      G i ≤ (j:ℤ)*D i := by
    intro i h
    have hmin : G i ≤ min 0 (D i) := by omega
    have hcases : j=0 ∨ j=1 := by omega
    rcases hcases with h0 | h1
    · subst j
      simp only [Nat.cast_zero,zero_mul]
      exact hmin.trans (min_le_left _ _)
    · subst j
      simp only [Nat.cast_one,one_mul]
      exact hmin.trans (min_le_right _ _)
  constructor
  · intro h i
    by_cases hi : 0 < G i-min 0 (D i)
    · rw [← same i hi]; exact h i
    · have hb := trivialGuard i hi
      linarith [nn' i]
  · intro h i
    by_cases hi : 0 < G i-min 0 (D i)
    · rw [same i hi]; exact h i
    · have hb := trivialGuard i hi
      linarith [nn i]

theorem cooldown_two_stable {ι : Type*} (v v' D G : ι → ℤ)
    (H : List (ι → ℤ)) (nn : ∀ i, 0 ≤ v i) (nn' : ∀ i, 0 ≤ v' i)
    (sameG : ∀ i, 0 < G i-min 0 (D i) → v i=v' i)
    (sameH : ∀ g ∈ H, ∀ i, 0 < g i-min 0 (D i) → v i=v' i) :
    repeatOK v D G H 2 ↔ repeatOK v' D G H 2 := by
  constructor
  · intro h j hj
    obtain ⟨g,hh⟩ := h j hj
    exact ⟨(guard_two_stable v v' D G nn nn' sameG j hj).mp g,
      fun a ha a' => hh a ha ((guard_two_stable v v' D a nn nn' (sameH a ha) j hj).mpr a')⟩
  · intro h j hj
    obtain ⟨g,hh⟩ := h j hj
    exact ⟨(guard_two_stable v v' D G nn nn' sameG j hj).mpr g,
      fun a ha a' => hh a ha ((guard_two_stable v v' D a nn nn' (sameH a ha) j hj).mp a')⟩

-- Admission only pays a particular charged prefix. Later unsuccessful
-- discovery can still cost work, so no global no-regression theorem.
theorem admission_prefix (unchanged overhead lower literal : Nat)
    (paid : overhead ≤ lower) (bound : lower ≤ literal) :
    unchanged+overhead ≤ unchanged+literal :=
  Nat.add_le_add_left (paid.trans bound) unchanged

end PNPGuardedTranslation
