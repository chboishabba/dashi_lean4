/-
# The literal dyadic critical weight of the periodic-B control cut

The B-lane control cut of 2026-09-15 fixes the critical multiplier of the
finite Galerkin observables to be the *rational dyadic shell weight*

  `w(k) = 2 ^ shellIndex k`,   `shellIndex k = ⌈log₂ |k|_∞⌉`,

with `|k|_∞` the exact integer max-coordinate norm (`waveMaxCoord`) already used
by the lattice-counting lane of this project.  This file installs that weight in
the Lean carrier and pays, as theorems, the two shell bounds that the Agda owner
`NSTriadKNLiteralDyadicShellConstants` carries as *fields* of the record
`DyadicShellBounds`:

* `waveMaxCoord_le_critWeight` — the shell upper law `|k|_∞ ≤ 2^{shellIndex k}`;
* `critWeight_le_two_mul` — the shell lower law in multiplicative form,
  `2^{shellIndex k} ≤ 2|k|_∞` for `k ≠ 0`.

It also proves the transfer inequality a triad estimate actually consumes,

* `critWeight_add_le` — `w(p+q) ≤ 2 (w p + w q)`,

and the negative summation fact that rules out closing the S2b estimate by a
Wiener / `ℓ¹` majorisation:

* `exists_sum_inv_critWeight_ge` — the `ℓ¹` mass `∑ 1/w(k)` over nonzero modes of
  the max-norm box of radius `N` is at least `N/2`, hence unbounded in the
  Galerkin cutoff.

Nothing here is an estimate on a velocity field; this is the exact weight
geometry.
-/
import RequestProject.NavierStokes.LatticeShellCounting

noncomputable section

open Finset

namespace ClayNS.Waleffe

/-! ## The dyadic shell index and its weight -/

/-- The literal shell index `⌈log₂ |k|_∞⌉` of a lattice wave, with the zero mode
mapped to shell `0` exactly as in the Agda owner. -/
def critShell (k : Wave) : ℕ := Nat.clog 2 (waveMaxCoord k)

/-- The literal rational dyadic critical multiplier `w(k) = 2 ^ shellIndex k`. -/
def critWeight (k : Wave) : ℝ := 2 ^ critShell k

theorem critWeight_pos (k : Wave) : 0 < critWeight k := by
  unfold critWeight; positivity

theorem one_le_critWeight (k : Wave) : 1 ≤ critWeight k := by
  unfold critWeight
  exact one_le_pow₀ (by norm_num)

theorem critWeight_nonneg (k : Wave) : 0 ≤ critWeight k := (critWeight_pos k).le

/-- **Shell upper law.**  `|k|_∞ ≤ 2 ^ shellIndex k`. -/
theorem waveMaxCoord_le_critWeight (k : Wave) : (waveMaxCoord k : ℝ) ≤ critWeight k := by
  have h : waveMaxCoord k ≤ 2 ^ Nat.clog 2 (waveMaxCoord k) := Nat.le_pow_clog (by norm_num) _
  calc (waveMaxCoord k : ℝ) ≤ ((2 ^ Nat.clog 2 (waveMaxCoord k) : ℕ) : ℝ) := by exact_mod_cast h
    _ = critWeight k := by simp [critWeight, critShell]

/-- **Shell lower law, multiplicative form.**  For a nonzero mode
`2 ^ shellIndex k ≤ 2 |k|_∞`. -/
theorem critWeight_le_two_mul {k : Wave} (hk : k ≠ 0) :
    critWeight k ≤ 2 * (waveMaxCoord k : ℝ) := by
  have h1 : 1 ≤ waveMaxCoord k := waveMaxCoord_pos_of_ne_zero hk
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · have hs : critShell k = 0 := by simp [critShell, ← h]
    rw [critWeight, hs, ← h]
    norm_num
  · have hlt : 2 ^ (Nat.clog 2 (waveMaxCoord k) - 1) < waveMaxCoord k :=
      Nat.pow_pred_clog_lt_self (by norm_num) h
    have hc : 0 < Nat.clog 2 (waveMaxCoord k) := Nat.clog_pos (by norm_num) h
    have hsplit : (2 : ℕ) ^ Nat.clog 2 (waveMaxCoord k)
        = 2 * 2 ^ (Nat.clog 2 (waveMaxCoord k) - 1) := by
      conv_lhs => rw [show Nat.clog 2 (waveMaxCoord k)
        = (Nat.clog 2 (waveMaxCoord k) - 1) + 1 by omega]
      ring
    have hnat : (2 : ℕ) ^ Nat.clog 2 (waveMaxCoord k) ≤ 2 * waveMaxCoord k := by
      rw [hsplit]; omega
    calc critWeight k = ((2 ^ Nat.clog 2 (waveMaxCoord k) : ℕ) : ℝ) := by
          simp [critWeight, critShell]
      _ ≤ ((2 * waveMaxCoord k : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 2 * (waveMaxCoord k : ℝ) := by push_cast; ring

theorem critShell_mono {p q : Wave} (h : waveMaxCoord p ≤ waveMaxCoord q) :
    critShell p ≤ critShell q :=
  Nat.clog_mono_right _ h

theorem waveMaxCoord_add_le (p q : Wave) :
    waveMaxCoord (p + q) ≤ waveMaxCoord p + waveMaxCoord q := by
  refine waveMaxCoord_le_iff.2 fun i => ?_
  have h1 : (p i).natAbs ≤ waveMaxCoord p := waveMaxCoord_le_iff.1 le_rfl i
  have h2 : (q i).natAbs ≤ waveMaxCoord q := waveMaxCoord_le_iff.1 le_rfl i
  have h3 : ((p + q) i).natAbs ≤ (p i).natAbs + (q i).natAbs := by
    simpa using Int.natAbs_add_le (p i) (q i)
  omega

theorem critWeight_zero : critWeight (0 : Wave) = 1 := by
  have h : waveMaxCoord (0 : Wave) = 0 := by simp [waveMaxCoord]
  simp [critWeight, critShell, h]

/-- **Transfer bound for the dyadic weight.**  On a resonant triad `k = p + q`
the output weight is controlled by the input weights: `w(p+q) ≤ 2 (w p + w q)`.
Proved from the two shell laws. -/
theorem critWeight_add_le (p q : Wave) :
    critWeight (p + q) ≤ 2 * (critWeight p + critWeight q) := by
  rcases eq_or_ne (p + q) 0 with h | h
  · rw [h, critWeight_zero]
    have hp := one_le_critWeight p
    have hq := one_le_critWeight q
    linarith
  · have h1 : critWeight (p + q) ≤ 2 * (waveMaxCoord (p + q) : ℝ) := critWeight_le_two_mul h
    have h2 : (waveMaxCoord (p + q) : ℝ) ≤ (waveMaxCoord p : ℝ) + (waveMaxCoord q : ℝ) := by
      exact_mod_cast waveMaxCoord_add_le p q
    have h3 := waveMaxCoord_le_critWeight p
    have h4 := waveMaxCoord_le_critWeight q
    linarith

/-! ## No high-low commutator gain for the sharp dyadic weight -/

/-- The lattice wave `(n,0,0)`. -/
def axisWave (n : ℕ) : Wave := ![(n : ℤ), 0, 0]

theorem waveMaxCoord_axisWave (n : ℕ) : waveMaxCoord (axisWave n) = n := by
  simp [waveMaxCoord, axisWave]

theorem axisWave_add (m n : ℕ) : axisWave m + axisWave n = axisWave (m + n) := by
  funext i
  fin_cases i <;> simp [axisWave]

theorem axisWave_ne_zero {n : ℕ} (hn : 0 < n) : axisWave n ≠ 0 := by
  intro h
  have := waveMaxCoord_axisWave n
  rw [h] at this
  simp [waveMaxCoord] at this
  omega

theorem critWeight_axisWave (n : ℕ) : critWeight (axisWave n) = 2 ^ Nat.clog 2 n := by
  simp [critWeight, critShell, waveMaxCoord_axisWave]

/-- **The sharp dyadic weight admits no high-low commutator gain.**  Writing
`k = p + q` with `p` the *low* leg, the weight difference `w(k) − w(q)` is not
controlled by any fixed multiple of the low weight `w(p)`: with `|p|_∞ = 1` and
`|q|_∞ = 2^j` the difference is exactly `2^j`, while `w(p) = 1`.

So the shell-boundary jump of `w` cannot be absorbed by a Lipschitz/commutator
estimate in the low leg, and an S2b producer must either smooth the multiplier
(and pay the `R517` comparison) or exploit the signed structure on the
shell-boundary set.  This is a statement about the weight only; no velocity
field is involved. -/
theorem no_highlow_commutator_gain (C : ℝ) :
    ∃ p q : Wave, p ≠ 0 ∧ q ≠ 0 ∧ waveMaxCoord p = 1 ∧
      C * critWeight p < |critWeight (p + q) - critWeight q| := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (max C 0) (by norm_num : (1:ℝ) < 2)
  refine ⟨axisWave 1, axisWave (2 ^ j), axisWave_ne_zero one_pos,
    axisWave_ne_zero (Nat.two_pow_pos j), by simp [waveMaxCoord_axisWave], ?_⟩
  have hp : critWeight (axisWave 1) = 1 := by
    rw [critWeight_axisWave]
    simp
  have hq : critWeight (axisWave (2 ^ j)) = 2 ^ j := by
    rw [critWeight_axisWave, Nat.clog_pow 2 j (by norm_num)]
  have hk : critWeight (axisWave 1 + axisWave (2 ^ j)) = 2 ^ (j + 1) := by
    rw [axisWave_add, critWeight_axisWave]
    have hclog : Nat.clog 2 (1 + 2 ^ j) = j + 1 := by
      have hle : Nat.clog 2 (1 + 2 ^ j) ≤ j + 1 := by
        refine (Nat.clog_le_iff_le_pow (by norm_num)).2 ?_
        have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        calc 1 + 2 ^ j ≤ 2 ^ j + 2 ^ j := by omega
          _ = 2 ^ (j + 1) := by ring
      have hge : j + 1 ≤ Nat.clog 2 (1 + 2 ^ j) := by
        have : j < Nat.clog 2 (1 + 2 ^ j) := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by omega)
        omega
      omega
    rw [hclog]
  rw [hp, hq, hk, mul_one]
  have hdiff : |(2 : ℝ) ^ (j + 1) - 2 ^ j| = 2 ^ j := by
    have : (2 : ℝ) ^ (j + 1) - 2 ^ j = 2 ^ j := by ring
    rw [this, abs_of_nonneg (by positivity)]
  rw [hdiff]
  exact lt_of_le_of_lt (le_max_left _ _) hj

/-! ## The `ℓ¹` mass of the inverse weight is not cutoff-uniform -/

/-- The wave `(m, j, 0)`. -/
private def slabWave (m j : ℕ) : Wave := ![(m : ℤ), (j : ℤ), 0]

private theorem slabWave_maxCoord {m j : ℕ} (h : j ≤ m) : waveMaxCoord (slabWave m j) = m := by
  simp only [waveMaxCoord, slabWave, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Int.natAbs_natCast, Int.natAbs_zero]
  omega

private theorem slabWave_ne_zero {m j : ℕ} (h : j ≤ m) (hm : 1 ≤ m) : slabWave m j ≠ 0 := by
  intro h0
  have := slabWave_maxCoord h
  rw [h0] at this
  simp [waveMaxCoord] at this
  omega

private theorem inv_critWeight_slabWave_ge {m j : ℕ} (h : j ≤ m) (hm : 1 ≤ m) :
    (1 : ℝ) / (2 * m) ≤ (critWeight (slabWave m j))⁻¹ := by
  have hmax := slabWave_maxCoord h
  have hw : critWeight (slabWave m j) ≤ 2 * (m : ℝ) := by
    have := critWeight_le_two_mul (slabWave_ne_zero h hm)
    rwa [hmax] at this
  have hpos : (0 : ℝ) < critWeight (slabWave m j) := critWeight_pos _
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  rw [div_le_iff₀ h2]
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-- **No cutoff-uniform Wiener `ℓ¹` majorisation.**  The `ℓ¹` mass of the inverse
dyadic critical weight over nonzero modes of the max-norm box of radius `N` is at
least `N / 2`, hence unbounded in the Galerkin cutoff.  Any route that pays the
critical production by an `ℓ¹` majorisation of the inverse weight therefore loses
an unbounded factor — the exact content of the corpus flag
`round410AllowsWienerL1MajorizationAsFinalPayment = false`. -/
theorem exists_sum_inv_critWeight_ge (N : ℕ) :
    ∃ S : Finset Wave, (∀ k ∈ S, k ≠ 0 ∧ waveMaxCoord k ≤ N) ∧
      (N : ℝ) / 2 ≤ ∑ k ∈ S, (critWeight k)⁻¹ := by
  classical
  set idx : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 N).sigma (fun m => Finset.Icc 0 m) with hidx
  set f : ((_ : ℕ) × ℕ) → Wave := fun z => slabWave z.1 z.2 with hf
  have hmem : ∀ z ∈ idx, 1 ≤ z.1 ∧ z.1 ≤ N ∧ z.2 ≤ z.1 := by
    intro z hz
    rw [hidx, Finset.mem_sigma] at hz
    exact ⟨(Finset.mem_Icc.1 hz.1).1, (Finset.mem_Icc.1 hz.1).2, (Finset.mem_Icc.1 hz.2).2⟩
  have hinj : Set.InjOn f idx := by
    intro a ha b hb hab
    have h0 : (a.1 : ℤ) = (b.1 : ℤ) := congrFun hab 0
    have h1 : (a.2 : ℤ) = (b.2 : ℤ) := congrFun hab 1
    have e0 : a.1 = b.1 := by exact_mod_cast h0
    have e1 : a.2 = b.2 := by exact_mod_cast h1
    cases a; cases b; simp_all
  refine ⟨idx.image f, ?_, ?_⟩
  · intro k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨h1, h2, h3⟩ := hmem z hz
    refine ⟨slabWave_ne_zero h3 h1, ?_⟩
    rw [hf]
    rw [slabWave_maxCoord h3]
    exact h2
  · rw [Finset.sum_image fun a ha b hb h => hinj ha hb h]
    have hstep : ∀ m ∈ Finset.Icc 1 N,
        (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 0 m, (critWeight (slabWave m j))⁻¹ := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
      have hlow : ∀ j ∈ Finset.Icc 0 m,
          (1 : ℝ) / (2 * m) ≤ (critWeight (slabWave m j))⁻¹ := by
        intro j hj
        exact inv_critWeight_slabWave_ge (Finset.mem_Icc.1 hj).2 hm1
      have hsum := Finset.sum_le_sum hlow
      have hcard : (Finset.Icc 0 m).card = m + 1 := by simp
      have hconst : ∑ _j ∈ Finset.Icc 0 m, (1 : ℝ) / (2 * m) = (m + 1) * (1 / (2 * m)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring
      rw [hconst] at hsum
      have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hhalf : (1 : ℝ) / 2 ≤ ((m : ℝ) + 1) * (1 / (2 * m)) := by
        have h2m : (0 : ℝ) < 2 * (m : ℝ) := by linarith
        rw [mul_one_div, le_div_iff₀ h2m]
        linarith
      linarith
    have hsig : ∑ z ∈ idx, (critWeight (f z))⁻¹
        = ∑ m ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 0 m, (critWeight (slabWave m j))⁻¹ := by
      rw [hidx, Finset.sum_sigma]
    rw [hsig]
    have := Finset.sum_le_sum hstep
    have hcard : (Finset.Icc 1 N).card = N := by simp
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    calc (N : ℝ) / 2 = (N : ℝ) * (1 / 2) := by ring
      _ ≤ _ := this

end ClayNS.Waleffe
