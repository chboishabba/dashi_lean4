/-
# The remaining Wiener input is supercritical

`WaleffeWienerBudget.lean` reduces the Round 105 wall
`PhysicalWeightedPositiveWaleffeNetworkForcingBudget` to a single quantity of
the Galerkin flows,

`∫_0^T ‖u(t)‖_A³ ‖u(t)‖_D dt`,  `‖u‖_A = ∑_k |u_k|`,  `‖u‖_D = ∑_k |k| |u_k|`.

The only quantity that the Galerkin system supplies uniformly in the truncation
is the energy `∑_k |u_k|²` (together with its time-integrated dissipation).
This file proves that the energy does **not** control the Wiener norm: there are
kinematically admissible (transverse, mode-supported) fields of unit energy
whose Wiener norm is arbitrarily large.  The witnesses are the flat spectra on
`N` collinear modes, polarised orthogonally to them.

Hence the residual input of the reduction cannot be extracted from the energy
inequality; in this precise sense the network-forcing wall is supercritical, and
no rearrangement of the `ℓ¹` majorisation can avoid that.
-/
import RequestProject.NavierStokes.WaleffeWienerBudget

noncomputable section

namespace ClayNS.Waleffe

/-- The `j`-th collinear test wavevector `(j+1, 0, 0)`. -/
def modeVec (j : ℕ) : Wave := ![(j + 1 : ℤ), 0, 0]

/-- The first `N` collinear test wavevectors. -/
def sampleModes (N : ℕ) : Finset Wave := (Finset.range N).image modeVec

/-- The single-mode amplitude of a flat spectrum of total energy one on `N`
modes, polarised along the second axis. -/
def sampleVec (N : ℕ) : Fin 3 → ℂ := ![0, ((Real.sqrt (1 / N) : ℝ) : ℂ), 0]

/-- The flat spectrum of total energy one on `sampleModes N`. -/
def sampleField (N : ℕ) : Wave → Fin 3 → ℂ := fun k =>
  if k ∈ sampleModes N then sampleVec N else fun _ => 0

theorem modeVec_injective : Function.Injective modeVec := by
  intro j j' h
  have := congrFun h 0
  simp only [modeVec, Matrix.cons_val_zero] at this
  omega

theorem card_sampleModes (N : ℕ) : (sampleModes N).card = N := by
  rw [sampleModes, Finset.card_image_of_injective _ modeVec_injective, Finset.card_range]

theorem zero_not_mem_sampleModes (N : ℕ) : (0 : Wave) ∉ sampleModes N := by
  intro h
  simp only [sampleModes, Finset.mem_image] at h
  obtain ⟨j, -, hj⟩ := h
  have := congrFun hj 0
  simp only [modeVec, Matrix.cons_val_zero, Pi.zero_apply] at this
  omega

theorem sampleModes_snd_zero {N : ℕ} {k : Wave} (hk : k ∈ sampleModes N) : k 1 = 0 := by
  simp only [sampleModes, Finset.mem_image] at hk
  obtain ⟨j, -, rfl⟩ := hk
  simp [modeVec]

theorem herm_wC_sampleVec (N : ℕ) {k : Wave} (h1 : k 1 = 0) :
    herm (wC k) (sampleVec N) = 0 := by
  simp only [herm, wC, sampleVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, h1]
  norm_num

theorem sampleField_transverse (N : ℕ) (k : Wave) : herm (wC k) (sampleField N k) = 0 := by
  by_cases hk : k ∈ sampleModes N
  · rw [sampleField, if_pos hk]
    exact herm_wC_sampleVec N (sampleModes_snd_zero hk)
  · simp [herm, sampleField, if_neg hk]

theorem sampleField_support (N : ℕ) (m : Wave) (hm : m ∉ sampleModes N) :
    sampleField N m = fun _ => 0 := by
  simp [sampleField, if_neg hm]

theorem nsq_sampleVec (N : ℕ) : nsq (sampleVec N) = 1 / N := by
  have hnn : (0 : ℝ) ≤ 1 / N := by positivity
  simp only [nsq, sampleVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num [Complex.normSq_ofReal, Real.mul_self_sqrt hnn]

theorem nsq_sampleField {N : ℕ} {k : Wave} (hk : k ∈ sampleModes N) :
    nsq (sampleField N k) = 1 / N := by
  rw [sampleField, if_pos hk, nsq_sampleVec]

theorem nrm_sampleField {N : ℕ} {k : Wave} (hk : k ∈ sampleModes N) :
    nrm (sampleField N k) = Real.sqrt (1 / N) := by
  rw [nrm, nsq_sampleField hk]

theorem energy_sampleField {N : ℕ} (hN : N ≠ 0) :
    ∑ k ∈ sampleModes N, nsq (sampleField N k) = 1 := by
  rw [Finset.sum_congr rfl fun k hk => nsq_sampleField hk, Finset.sum_const,
    card_sampleModes, nsmul_eq_mul]
  field_simp

theorem wienerA_sampleField (N : ℕ) :
    wienerA (sampleModes N) (sampleField N) = N * Real.sqrt (1 / N) := by
  rw [wienerA, Finset.sum_congr rfl fun k hk => nrm_sampleField hk, Finset.sum_const,
    card_sampleModes, nsmul_eq_mul]

theorem flat_spectrum_scale (N : ℕ) : (N : ℝ) * Real.sqrt (1 / N) = Real.sqrt N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
    rw [one_div, Real.sqrt_inv]
    field_simp
    exact (Real.sq_sqrt hN.le).symm

/-- **The Wiener norm is not controlled by the energy.**  For every `M` there is
a finite set of nonzero modes and a field supported on it, transverse to every
wavevector, of total energy one, whose Wiener norm exceeds `M`.  Consequently
the residual input `∫ ‖u‖_A³ ‖u‖_D` of the network-forcing reduction cannot be
obtained from the energy inequality alone. -/
theorem wiener_norm_not_controlled_by_energy (M : ℝ) :
    ∃ (modes : Finset Wave) (u : Wave → Fin 3 → ℂ),
      (0 : Wave) ∉ modes ∧
      (∀ k, herm (wC k) (u k) = 0) ∧
      (∀ m, m ∉ modes → u m = 0) ∧
      (∑ k ∈ modes, nsq (u k)) = 1 ∧
      M ≤ wienerA modes u := by
  obtain ⟨N, hN1, hNM⟩ : ∃ N : ℕ, N ≠ 0 ∧ M ≤ Real.sqrt N := by
    refine ⟨max 1 ⌈M ^ 2⌉₊, by positivity, ?_⟩
    have h1 : (M ^ 2 : ℝ) ≤ (⌈M ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈M ^ 2⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈M ^ 2⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_max_right 1 _
    calc M ≤ |M| := le_abs_self M
      _ = Real.sqrt (M ^ 2) := (Real.sqrt_sq_eq_abs M).symm
      _ ≤ Real.sqrt ((max 1 ⌈M ^ 2⌉₊ : ℕ) : ℝ) := Real.sqrt_le_sqrt (le_trans h1 h2)
  refine ⟨sampleModes N, sampleField N, zero_not_mem_sampleModes N,
    sampleField_transverse N, sampleField_support N, energy_sampleField hN1, ?_⟩
  rw [wienerA_sampleField, flat_spectrum_scale]
  exact hNM

/-! ## The exact cost of the `ℓ¹` route -/

/-- Cauchy–Schwarz: the Wiener norm costs exactly a factor `√(#modes)` over the
energy. -/
theorem wienerA_le_sqrt_card_energy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    wienerA modes u ≤ Real.sqrt modes.card * Real.sqrt (∑ k ∈ modes, nsq (u k)) := by
  have h := Real.sum_sqrt_mul_sqrt_le (f := fun _ : Wave => (1 : ℝ))
    (g := fun k => nsq (u k)) modes (fun _ => zero_le_one) (fun k => nsq_nonneg _)
  simpa [wienerA, nrm, Finset.sum_const, nsmul_eq_mul] using h

/-- Cauchy–Schwarz: the one-derivative Wiener norm costs exactly a factor
`√(#modes)` over the enstrophy. -/
theorem wienerD_le_sqrt_card_enstrophy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    wienerD modes u ≤ Real.sqrt modes.card * Real.sqrt (∑ k ∈ modes, wsq k * nsq (u k)) := by
  have hwsq : ∀ k : Wave, 0 ≤ wsq k := fun k =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h := Real.sum_sqrt_mul_sqrt_le (f := fun _ : Wave => (1 : ℝ))
    (g := fun k => wsq k * nsq (u k)) modes (fun _ => zero_le_one)
    (fun k => mul_nonneg (hwsq k) (nsq_nonneg _))
  have hterm : ∀ k ∈ modes, wlen k * nrm (u k) = Real.sqrt 1 * Real.sqrt (wsq k * nsq (u k)) := by
    intro k _
    rw [Real.sqrt_one, one_mul, wlen, nrm, Real.sqrt_mul (hwsq k)]
  rw [wienerD, Finset.sum_congr rfl hterm]
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- The `√(#modes)` loss is attained: the flat spectra saturate the
Cauchy–Schwarz bound.  So the reduction to the Wiener expenditure cannot be
repaired by a better use of the energy. -/
theorem flat_spectrum_saturates {N : ℕ} (hN : N ≠ 0) :
    wienerA (sampleModes N) (sampleField N)
      = Real.sqrt (sampleModes N).card
        * Real.sqrt (∑ k ∈ sampleModes N, nsq (sampleField N k)) := by
  rw [wienerA_sampleField, flat_spectrum_scale, energy_sampleField hN, card_sampleModes,
    Real.sqrt_one, mul_one]

end ClayNS.Waleffe
