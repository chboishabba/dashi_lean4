import RequestProject.CenterRetractionMore

/-!
# Which dihedral groups retract onto their center

The dihedral group `D_n` of order `2n` (`n ≠ 0`) admits a retraction onto its center **if and
only if `4 ∤ n`**:

* for `n` odd the center is trivial (`n = 1` gives an abelian group);
* for `n ≡ 2 (mod 4)` the center is `{1, r^(n/2)}` and the "parity of the rotation exponent"
  homomorphism is a retraction onto it (`hasCenterRetraction_dihedral_of_two_mod_four`);
* for `4 ∣ n` the central element `r^(n/2)` lies in the derived subgroup, so by
  `disjoint_commutator_center` no retraction can exist
  (`not_hasCenterRetraction_dihedral_of_four_dvd`).

The classification is `hasCenterRetraction_dihedral_iff`. Along the way the center of `D_n`
for even `n > 2` is computed: `DihedralGroup.mem_center_even_iff`.
-/

open Subgroup DihedralGroup

namespace DihedralGroup

/-- The center of `D_n` for even `n > 2` consists exactly of `1` and the half-turn
`r^(n/2)`. -/
theorem mem_center_even_iff (n : ℕ) (hn : 2 ∣ n) (hn2 : 2 < n) (x : DihedralGroup n) :
    x ∈ center (DihedralGroup n) ↔ (x = 1 ∨ x = r ((n / 2 : ℕ) : ZMod n)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hhalf : n = 2 * (n / 2) := by omega
  constructor
  · intro hx
    rw [mem_center_iff] at hx
    match x with
    | .sr j =>
        exfalso
        have h := hx (r 1)
        rw [r_mul_sr, sr_mul_r] at h
        simp only [DihedralGroup.sr.injEq] at h
        have h3 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination -h
        have hd := (ZMod.natCast_eq_zero_iff 2 n).1 h3
        have := Nat.le_of_dvd (by norm_num) hd
        omega
    | .r k =>
        have h := hx (sr 0)
        rw [r_mul_sr, sr_mul_r] at h
        simp only [DihedralGroup.sr.injEq] at h
        have hkk : k + k = 0 := by linear_combination h
        have h3 : ((2 * k.val : ℕ) : ZMod n) = 0 := by
          rw [Nat.cast_mul, ZMod.natCast_zmod_val]
          push_cast
          linear_combination hkk
        have hdvd := (ZMod.natCast_eq_zero_iff _ n).1 h3
        have hlt : k.val < n := ZMod.val_lt k
        have hcases : k.val = 0 ∨ k.val = n / 2 := by
          obtain ⟨c, hc⟩ := hdvd
          rcases Nat.lt_or_ge c 2 with hc2 | hc2
          · interval_cases c <;> omega
          · have : n * 2 ≤ n * c := Nat.mul_le_mul_left n hc2
            omega
        rcases hcases with h0 | h0
        · left
          have hk0 : k = 0 := by rw [← ZMod.natCast_zmod_val k, h0]; simp
          rw [hk0, one_def]
        · right
          congr 1
          rw [← ZMod.natCast_zmod_val k, h0]
  · rintro (rfl | rfl)
    · exact one_mem _
    · rw [mem_center_iff]
      rintro (j | j)
      · rw [r_mul_r, r_mul_r, add_comm]
      · rw [r_mul_sr, sr_mul_r]
        congr 1
        have h2 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
          have hc : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n)
              = ((n / 2 + n / 2 : ℕ) : ZMod n) := by push_cast; ring
          rw [hc, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
        linear_combination (norm := abel) h2

/-- The half-turn `r^(n/2)` is nontrivial for even `n > 2`. -/
theorem r_half_ne_one (n : ℕ) (hn : 2 ∣ n) (hn2 : 2 < n) :
    (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  rw [one_def] at h
  have h0 : ((n / 2 : ℕ) : ZMod n) = 0 := by
    simpa using congrArg (fun g => match g with
      | DihedralGroup.r i => i
      | DihedralGroup.sr i => i) h
  have hdvd := (ZMod.natCast_eq_zero_iff _ n).1 h0
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The parity of the rotation exponent, a `ZMod 2`-valued function on `D_n` for even `n`. -/
private def par {n : ℕ} (h : 2 ∣ n) : DihedralGroup n → ZMod 2
  | .r i => ZMod.castHom h (ZMod 2) i
  | .sr i => ZMod.castHom h (ZMod 2) i

private theorem par_mul {n : ℕ} (h : 2 ∣ n) (g g' : DihedralGroup n) :
    par h (g * g') = par h g + par h g' := by
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  match g, g' with
  | .r i, .r j => simp only [par, r_mul_r, map_add]
  | .r i, .sr j =>
      simp only [par, r_mul_sr, map_sub]
      rw [sub_eq_add_neg, hneg, add_comm]
  | .sr i, .r j => simp only [par, sr_mul_r, map_add]
  | .sr i, .sr j =>
      simp only [par, sr_mul_sr, map_sub]
      rw [sub_eq_add_neg, hneg, add_comm]

/-- **Positive case.** If `n ≡ 2 (mod 4)` (i.e. `n` is even and `n / 2` is odd) and `n > 2`,
then `D_n` retracts onto its center: the parity of the rotation exponent is a homomorphism
onto `{1, r^(n/2)}` which fixes it pointwise. -/
theorem hasCenterRetraction_dihedral_of_two_mod_four (n : ℕ) (hn : 2 ∣ n) (hn2 : 2 < n)
    (hodd : Odd (n / 2)) : HasCenterRetraction (DihedralGroup n) := by
  classical
  have hz : (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∈ center (DihedralGroup n) :=
    (mem_center_even_iff n hn hn2 _).2 (Or.inr rfl)
  set zc : center (DihedralGroup n) := ⟨r ((n / 2 : ℕ) : ZMod n), hz⟩ with hzc
  have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    have hcc : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n)
        = ((n / 2 + n / 2 : ℕ) : ZMod n) := by push_cast; ring
    rw [hcc, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
  have hzz : zc * zc = 1 := by
    apply Subtype.ext
    show (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) * r ((n / 2 : ℕ) : ZMod n) = 1
    rw [r_mul_r, hhalf, r_zero]
  have hpar1 : par hn (1 : DihedralGroup n) = 0 := by
    rw [one_def]
    simp [par]
  have hparz : par hn (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) = 1 := by
    show ZMod.castHom hn (ZMod 2) ((n / 2 : ℕ) : ZMod n) = 1
    rw [map_natCast]
    obtain ⟨t, ht⟩ := hodd
    rw [ht]
    push_cast
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
    push_cast at h2
    rw [h2]
    ring
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hne : (1 : ZMod 2) ≠ 0 := by decide
  have hsum : (1 : ZMod 2) + 1 = 0 := by decide
  refine ⟨⟨⟨fun g => if par hn g = 0 then 1 else zc, by simp [hpar1]⟩, ?_⟩, ?_⟩
  · intro a b
    simp only [par_mul]
    rcases hcases (par hn a) with ha | ha <;> rcases hcases (par hn b) with hb | hb <;>
      simp [ha, hb, hne, hsum, hzz]
  · rintro ⟨w, hw⟩
    rcases (mem_center_even_iff n hn hn2 w).1 hw with rfl | rfl
    · apply Subtype.ext
      simp [hpar1]
    · apply Subtype.ext
      show (if par hn (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) = 0 then
        (1 : center (DihedralGroup n)) else zc).val = _
      rw [hparz, if_neg hne]

/-- **Negative case.** If `4 ∣ n` (and `n ≠ 0`) then the central half-turn `r^(n/2)` is a
power of the commutator `⁅s, r⁆ = r^(-2)`, so it lies in the derived subgroup; since a
retraction onto the center makes those two subgroups meet trivially, `D_n` has no retraction
onto its center. -/
theorem not_hasCenterRetraction_dihedral_of_four_dvd (n : ℕ) (h4 : 4 ∣ n) (hn0 : n ≠ 0) :
    ¬ HasCenterRetraction (DihedralGroup n) := by
  have hn : 2 ∣ n := dvd_trans (by norm_num) h4
  have hn2 : 2 < n := by
    obtain ⟨c, rfl⟩ := h4
    have : c ≠ 0 := by rintro rfl; simp at hn0
    omega
  rintro ⟨ret, hret⟩
  have hz : (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∈ center (DihedralGroup n) :=
    (mem_center_even_iff n hn hn2 _).2 (Or.inr rfl)
  -- the half-turn is a power of a commutator
  have hc : (⁅(sr 0 : DihedralGroup n), (r 1 : DihedralGroup n)⁆) = r (-2) := by
    rw [commutatorElement_def, sr_mul_r, inv_sr, inv_r, sr_mul_sr, r_mul_r]
    congr 1
    ring
  have hpow : (⁅(sr 0 : DihedralGroup n), (r 1 : DihedralGroup n)⁆) ^ (n / 4)
      = r ((n / 2 : ℕ) : ZMod n) := by
    rw [hc, r_pow]
    congr 1
    have h1 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
      have hcc : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n)
          = ((n / 2 + n / 2 : ℕ) : ZMod n) := by push_cast; ring
      rw [hcc, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
    have h2 : ((n / 4 : ℕ) : ZMod n) + ((n / 4 : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by
      have hcc : ((n / 4 : ℕ) : ZMod n) + ((n / 4 : ℕ) : ZMod n)
          = ((n / 4 + n / 4 : ℕ) : ZMod n) := by push_cast; ring
      rw [hcc, show n / 4 + n / 4 = n / 2 by omega]
    linear_combination -h2 - h1
  have hmem : (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∈ commutator (DihedralGroup n) := by
    rw [← hpow]
    exact pow_mem (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _)) _
  have hdisj := disjoint_commutator_center hret
  have hone : (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) = 1 := by
    have : (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∈
        commutator (DihedralGroup n) ⊓ center (DihedralGroup n) := ⟨hmem, hz⟩
    rw [disjoint_iff.1 hdisj] at this
    simpa using this
  exact r_half_ne_one n hn hn2 hone

/-- **Classification.** For `n ≠ 0`, the dihedral group `D_n` of order `2n` retracts onto its
center if and only if `4` does not divide `n`. -/
theorem hasCenterRetraction_dihedral_iff (n : ℕ) (hn0 : n ≠ 0) :
    HasCenterRetraction (DihedralGroup n) ↔ ¬ (4 ∣ n) := by
  constructor
  · intro h h4
    exact not_hasCenterRetraction_dihedral_of_four_dvd n h4 hn0 h
  · intro h4
    rcases Nat.lt_or_ge n 3 with hsmall | hbig
    · -- `D₁` and `D₂` are abelian
      have hcomm : ∀ a b : DihedralGroup n, a * b = b * a := by
        have : n = 1 ∨ n = 2 := by omega
        have hstd : Std.Commutative (fun x y : DihedralGroup n => x * y) :=
          DihedralGroup.commutative_iff.2 this
        exact fun a b => hstd.comm a b
      exact hasCenterRetraction_of_commute hcomm
    · rcases Nat.even_or_odd n with hev | hodd
      · have hn : 2 ∣ n := hev.two_dvd
        have hhalfodd : Odd (n / 2) := by
          rcases Nat.even_or_odd (n / 2) with he | ho
          · have h2 : 2 ∣ n / 2 := he.two_dvd
            exact absurd (by omega : 4 ∣ n) h4
          · exact ho
        exact hasCenterRetraction_dihedral_of_two_mod_four n hn (by omega) hhalfodd
      · exact hasCenterRetraction_of_center_eq_bot
          (DihedralGroup.center_eq_bot_of_odd_ne_one hodd (by omega))

/-- `D₆` (order `12`, nonabelian, center of order `2`) retracts onto its center. -/
theorem hasCenterRetraction_dihedral_six : HasCenterRetraction (DihedralGroup 6) :=
  (hasCenterRetraction_dihedral_iff 6 (by norm_num)).2 (by decide)

/-- `D₄` (order `8`) does not, recovering the `p`-group obstruction. -/
theorem not_hasCenterRetraction_dihedral_four' : ¬ HasCenterRetraction (DihedralGroup 4) :=
  (hasCenterRetraction_dihedral_iff 4 (by norm_num)).not.mpr (by simp)

end DihedralGroup
