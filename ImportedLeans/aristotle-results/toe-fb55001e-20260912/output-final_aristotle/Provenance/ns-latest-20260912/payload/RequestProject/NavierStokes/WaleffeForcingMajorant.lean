/-
# A literal kinematic majorant for the Waleffe network forcing

`WaleffeNetworkForcingBudget.lean` states the open Round 105 wall: a
cutoff-uniform bound for the weighted positive network-forcing expenditure

  `∑_τ w_τ ∫_0^T (F_τ)₊ dt`.

This file *sharpens* the wall by removing every remaining abstraction from the
right-hand side: the network forcing of the literal physical Galerkin system is
bounded, pointwise in time and with explicit constants, by a purely kinematic
quartic expression in the Fourier coefficients,

  `|F_(k,p,q)| ≤ N_k ‖u_p‖ ‖u_q‖ + ‖u_k‖ N_p ‖u_q‖ + ‖u_k‖ ‖u_p‖ N_q`,
  `N_k := ∑_{p'∈Λ} ‖u_{p'}‖ · |k−p'| · ‖u_{k−p'}‖`,

obtained from
* the Lagrange/Cauchy amplitude bound (`abs_netForcing_le`),
* the contraction property of the Leray projection (`nrm_leray_le`),
* the triangle inequality and Cauchy–Schwarz for the truncated convolution.

Two consequences are worth recording.

*The naive majorant is supercritical.*  Every factor `|k−p'|` is a full
derivative, so `N_k` is at the level of `‖u‖·‖∇u‖` in an `ℓ¹` (not `ℓ²`)
convolution: summing the majorant over the whole triad network at the critical
weights costs strictly more than the energy/dissipation pair provides.  The
budget therefore cannot be obtained by termwise majorization; any proof must
use the cancellation carried by the *positive part* after global summation
(exactly the mechanism Round 105 isolates), not the absolute value.

*The wall is quartic in the amplitude.*  `homogeneity` records that the modal
forcing is quadratic and the network forcing quartic under `u ↦ c·u`, while the
energy is quadratic; so no bound for the budget can be deduced from an
energy-level a priori estimate by scaling alone.
-/
import RequestProject.NavierStokes.WaleffeNetworkForcingBudget

noncomputable section

namespace ClayNS.Waleffe

/-! ## Norm plumbing for `ℂ³` -/

theorem nrm_eq_norm (u : Fin 3 → ℂ) :
    nrm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq, nrm, nsq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.sq_norm]

theorem nrm_add_le (u v : Fin 3 → ℂ) : nrm (fun i => u i + v i) ≤ nrm u + nrm v := by
  rw [nrm_eq_norm, nrm_eq_norm, nrm_eq_norm]
  have h : (WithLp.toLp 2 (fun i => u i + v i) : EuclideanSpace ℂ (Fin 3))
      = WithLp.toLp 2 u + WithLp.toLp 2 v := rfl
  rw [h]
  exact norm_add_le _ _

theorem nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℂ) :
    nrm (fun i => ∑ a ∈ s, f a i) ≤ ∑ a ∈ s, nrm (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [nrm, nsq]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : nrm (fun i => ∑ b ∈ insert a s, f b i)
          = nrm (fun i => f a i + ∑ b ∈ s, f b i) := by
        congr 1
        funext i
        rw [Finset.sum_insert ha]
      rw [h1]
      exact le_trans (nrm_add_le _ _) (by linarith [ih])

theorem nrm_const_mul (c : ℂ) (v : Fin 3 → ℂ) : nrm (fun i => c * v i) = ‖c‖ * nrm v := by
  rw [nrm_eq_norm, nrm_eq_norm]
  have h : (WithLp.toLp 2 (fun i => c * v i) : EuclideanSpace ℂ (Fin 3))
      = c • WithLp.toLp 2 v := rfl
  rw [h, norm_smul]

/-- Cauchy–Schwarz for the (bilinear) contraction of two complex 3-vectors. -/
theorem abs_bilin_le (u w : Fin 3 → ℂ) : ‖∑ j, u j * w j‖ ≤ nrm u * nrm w := by
  have hinner : (inner ℂ
      (WithLp.toLp 2 (fun j => (starRingEnd ℂ) (u j)) : EuclideanSpace ℂ (Fin 3))
      (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))) = ∑ j, u j * w j := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 (fun j => (starRingEnd ℂ) (u j)) : EuclideanSpace ℂ (Fin 3))
    (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))
  rw [hinner] at h
  have hn : nrm (fun j => (starRingEnd ℂ) (u j)) = nrm u := by simp [nrm, nsq]
  rw [← nrm_eq_norm, ← nrm_eq_norm, hn] at h
  exact h

theorem nrm_wC (k : Wave) : nrm (wC k) = wlen k := by
  unfold nrm nsq wC wlen wsq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply]
  ring

/-! ## The Leray projection is a contraction -/

theorem herm_add_left (u v w : Fin 3 → ℂ) :
    herm (fun i => u i + v i) w = herm u w + herm v w := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_smul_left (c : ℂ) (u v : Fin 3 → ℂ) :
    herm (fun i => c * u i) v = (starRingEnd ℂ) c * herm u v := by
  simp [herm, Finset.mul_sum]
  congr 1
  funext i
  ring

/-- Orthogonal additivity of the squared norm. -/
theorem nsq_add_of_herm_zero (a b : Fin 3 → ℂ) (h : herm a b = 0) :
    nsq (fun i => a i + b i) = nsq a + nsq b := by
  have hba : herm b a = 0 := by
    have h2 := herm_conj a b
    rw [h] at h2
    simpa using h2.symm
  have hexp : ((nsq (fun i => a i + b i) : ℝ) : ℂ) = ((nsq a : ℝ) : ℂ) + ((nsq b : ℝ) : ℂ) := by
    rw [← herm_self, ← herm_self, ← herm_self, herm_add_left, herm_add_right, herm_add_right,
      h, hba]
    ring
  exact_mod_cast hexp

/-- Pythagoras for the Leray splitting: the projected part and the longitudinal
part are orthogonal. -/
theorem nsq_leray_add (k : Wave) (v : Fin 3 → ℂ) (hk : wsq k ≠ 0) :
    nsq v = nsq (leray k v)
      + nsq (fun i => (herm (wC k) v / (wsq k : ℂ)) * wC k i) := by
  have hab : herm (leray k v) (fun i => (herm (wC k) v / (wsq k : ℂ)) * wC k i) = 0 := by
    have h0 : herm (leray k v) (wC k) = 0 := by
      have h1 := herm_wC_leray k v hk
      have h2 := herm_conj (wC k) (leray k v)
      rw [h1] at h2
      simpa using h2.symm
    rw [herm_smul_right, h0, mul_zero]
  have h := nsq_add_of_herm_zero (leray k v)
    (fun i => (herm (wC k) v / (wsq k : ℂ)) * wC k i) hab
  rw [← h]
  congr 1
  funext i
  simp [leray, wC]

theorem nsq_leray_le (k : Wave) (v : Fin 3 → ℂ) (hk : wsq k ≠ 0) :
    nsq (leray k v) ≤ nsq v := by
  have h := nsq_leray_add k v hk
  have h2 := nsq_nonneg (fun i => (herm (wC k) v / (wsq k : ℂ)) * wC k i)
  linarith

theorem nrm_leray_le (k : Wave) (v : Fin 3 → ℂ) (hk : wsq k ≠ 0) :
    nrm (leray k v) ≤ nrm v :=
  Real.sqrt_le_sqrt (nsq_leray_le k v hk)

theorem nrm_neg (v : Fin 3 → ℂ) : nrm (fun i => -(v i)) = nrm v := by
  simp [nrm, nsq]

/-! ## The kinematic majorant of the modal forcing -/

/-- The `ℓ¹` convolution majorant of the modal forcing at the wavevector `k`. -/
def forcingMajorant (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k : Wave) : ℝ :=
  ∑ p ∈ modes, nrm (u p) * wlen (k - p) * nrm (u (k - p))

/-- **The literal modal forcing is bounded by the `ℓ¹` convolution majorant.**
One derivative appears in every term (through `|k−p|`); this is the exact
supercritical cost of termwise majorization. -/
theorem nrm_modalForcing_le (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k : Wave)
    (hk : wsq k ≠ 0) :
    nrm (modalForcing modes u k) ≤ forcingMajorant modes u k := by
  have h1 : nrm (modalForcing modes u k) = nrm (leray k (advection modes u k)) := by
    have he : modalForcing modes u k = fun i => -(leray k (advection modes u k) i) := rfl
    rw [he]
    exact nrm_neg _
  have h2 : nrm (leray k (advection modes u k)) ≤ nrm (advection modes u k) :=
    nrm_leray_le k _ hk
  have h3 : nrm (advection modes u k)
      ≤ ∑ p ∈ modes, nrm (fun i => (Complex.I * (∑ j, u p j * (((k - p) j : ℤ) : ℂ)))
          * u (k - p) i) := by
    exact nrm_sum_le modes _
  have h4 : ∀ p ∈ modes,
      nrm (fun i => (Complex.I * (∑ j, u p j * (((k - p) j : ℤ) : ℂ))) * u (k - p) i)
        ≤ nrm (u p) * wlen (k - p) * nrm (u (k - p)) := by
    intro p _
    rw [nrm_const_mul]
    have hI : ‖Complex.I * (∑ j, u p j * (((k - p) j : ℤ) : ℂ))‖
        = ‖∑ j, u p j * (((k - p) j : ℤ) : ℂ)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have hcs : ‖∑ j, u p j * (((k - p) j : ℤ) : ℂ)‖ ≤ nrm (u p) * wlen (k - p) := by
      have := abs_bilin_le (u p) (wC (k - p))
      rwa [nrm_wC] at this
    have hpos : 0 ≤ nrm (u (k - p)) := nrm_nonneg _
    rw [hI]
    calc ‖∑ j, u p j * (((k - p) j : ℤ) : ℂ)‖ * nrm (u (k - p))
        ≤ (nrm (u p) * wlen (k - p)) * nrm (u (k - p)) := by
          exact mul_le_mul_of_nonneg_right hcs hpos
      _ = nrm (u p) * wlen (k - p) * nrm (u (k - p)) := by ring
  have h5 := Finset.sum_le_sum h4
  rw [h1]
  rw [forcingMajorant]
  linarith [h2, h3, h5]

/-- **The kinematic majorant of the network forcing of a triad.**  Every object
on the right-hand side is an explicit function of the Fourier coefficients at
the given time: no dynamics and no abstraction remain. -/
theorem force3_majorant (G : GalerkinFlow) (k p q : Wave) (t : ℝ)
    (hk : wsq k ≠ 0) (hp : wsq p ≠ 0) (hq : wsq q ≠ 0) :
    |G.force3 k p q t|
      ≤ forcingMajorant G.modes (G.u t) k * nrm (G.u t p) * nrm (G.u t q)
        + nrm (G.u t k) * forcingMajorant G.modes (G.u t) p * nrm (G.u t q)
        + nrm (G.u t k) * nrm (G.u t p) * forcingMajorant G.modes (G.u t) q := by
  have hbase := abs_netForcing_le (G.u t k) (G.u t p) (G.u t q)
    (G.force t k) (G.force t p) (G.force t q)
  have hfk : nrm (G.force t k) ≤ forcingMajorant G.modes (G.u t) k :=
    nrm_modalForcing_le _ _ _ hk
  have hfp : nrm (G.force t p) ≤ forcingMajorant G.modes (G.u t) p :=
    nrm_modalForcing_le _ _ _ hp
  have hfq : nrm (G.force t q) ≤ forcingMajorant G.modes (G.u t) q :=
    nrm_modalForcing_le _ _ _ hq
  have hnk := nrm_nonneg (G.u t k)
  have hnp := nrm_nonneg (G.u t p)
  have hnq := nrm_nonneg (G.u t q)
  have e1 : nrm (G.force t k) * nrm (G.u t p) * nrm (G.u t q)
      ≤ forcingMajorant G.modes (G.u t) k * nrm (G.u t p) * nrm (G.u t q) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfk hnp) hnq
    linarith
  have e2 : nrm (G.u t k) * nrm (G.force t p) * nrm (G.u t q)
      ≤ nrm (G.u t k) * forcingMajorant G.modes (G.u t) p * nrm (G.u t q) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfp hnk) hnq
    linarith
  have e3 : nrm (G.u t k) * nrm (G.u t p) * nrm (G.force t q)
      ≤ nrm (G.u t k) * nrm (G.u t p) * forcingMajorant G.modes (G.u t) q := by
    have := mul_le_mul_of_nonneg_left hfq (mul_nonneg hnk hnp)
    linarith
  have hf3 : G.force3 k p q t
      = netForcing (G.u t k) (G.u t p) (G.u t q) (G.force t k) (G.force t p) (G.force t q) := rfl
  rw [hf3]
  linarith

/-! ## Homogeneity: the wall is quartic while the energy is quadratic -/

theorem advection_smul (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℂ) (k : Wave) :
    advection modes (fun p i => c * u p i) k = fun i => c ^ 2 * advection modes u k i := by
  funext i
  simp only [advection, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : (∑ j, Complex.I * (c * u p j * (((k - p) j : ℤ) : ℂ)))
      = c * ∑ j, Complex.I * (u p j * (((k - p) j : ℤ) : ℂ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  ring

theorem leray_smul (k : Wave) (c : ℂ) (v : Fin 3 → ℂ) :
    leray k (fun i => c * v i) = fun i => c * leray k v i := by
  funext i
  simp only [leray, herm_smul_right]
  ring

/-- The modal forcing is quadratically homogeneous in the field. -/
theorem modalForcing_smul (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (c : ℂ) (k : Wave) :
    modalForcing modes (fun p i => c * u p i) k = fun i => c ^ 2 * modalForcing modes u k i := by
  funext i
  show -(leray k (advection modes (fun p i => c * u p i) k) i)
      = c ^ 2 * -(leray k (advection modes u k) i)
  rw [advection_smul, leray_smul]
  ring

/-- The network forcing is quartically homogeneous in the field, while the
energy is quadratic: no scaling argument from an energy-level a priori bound
can produce the budget. -/
theorem netForcingC_smul (uK uP uQ fK fP fQ : Fin 3 → ℂ) (c : ℝ) :
    netForcingC (fun i => (c : ℂ) * uK i) (fun i => (c : ℂ) * uP i) (fun i => (c : ℂ) * uQ i)
        (fun i => (c : ℂ) ^ 2 * fK i) (fun i => (c : ℂ) ^ 2 * fP i)
        (fun i => (c : ℂ) ^ 2 * fQ i)
      = (c : ℂ) ^ 4 * netForcingC uK uP uQ fK fP fQ := by
  simp only [netForcingC, herm, cross, crossProduct, Fin.sum_univ_three,
    LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_mul, map_pow, Complex.conj_ofReal]
  ring

theorem netForcing_smul (uK uP uQ fK fP fQ : Fin 3 → ℂ) (c : ℝ) :
    netForcing (fun i => (c : ℂ) * uK i) (fun i => (c : ℂ) * uP i) (fun i => (c : ℂ) * uQ i)
        (fun i => (c : ℂ) ^ 2 * fK i) (fun i => (c : ℂ) ^ 2 * fP i)
        (fun i => (c : ℂ) ^ 2 * fQ i)
      = c ^ 4 * netForcing uK uP uQ fK fP fQ := by
  show (netForcingC _ _ _ _ _ _).re = _
  rw [netForcingC_smul, show ((c : ℂ) ^ 4) = ((c ^ 4 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]
  rfl

end ClayNS.Waleffe
