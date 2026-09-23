/-
# Row A — the history-free fork: when the Gaussian shell coefficient carries no
bare-coupling dependence, the contraction constant is purely the interaction
sensitivity

`RowASmallBareCoupling` produces the Row-A completion predicate at every
sufficiently small bare coupling from a hypothesis package that still contains a
*memory* sector: the shell coefficients are allowed to depend on the bare
inverse coupling `u₀` through the irrelevant renormalisation-group state, and
that dependence is controlled by the Duhamel constant `C_mem` and the
coefficient-to-state Lipschitz constant `L_coef`.

There is a strategic fork here that is worth recording as a theorem.  In the
literal source normalisation the Gaussian shell coefficient `β_Z` and the five
channel data (`λ_det`, `λ_gauge`, and the three Cauchy families) are attached to
the *scale* `j`, not to the bare coupling: the bare coupling enters the shell
coefficient only through the running coupling `g_j`, which is the marginal
coordinate the shooting map already tracks explicitly.  Whenever that is the
case — i.e. whenever

    ∂_u β_Z = 0   and   ∂_u (channel data) = 0   at fixed scale

— the memory sector is *empty*: `L_coef = 0`, `C_mem = 0`, and the whole
cumulative sensitivity is the resummed direct marginal weight

    σ = Σ_j (C_dir/2)·g_j⁶ ≤ (C_dir/2)·(u₀⁻³ + 1/(2 b u₀²)),

so the contraction constant obeys `q ≤ 2σ ≲ C_dir(1 + 1/(2b))/u₀²` and `q < 1`
holds as soon as the bare coupling is small enough.  This is exactly the
"almost automatic" branch of the fork: no exponential-forgetting law is imposed
on any coordinate, marginal or not, because no coordinate is asked to forget.

Contents.

* `literalKernelMass_history_free` — with `C_mem = 0` the kernel mass is exactly
  the resummed marginal weight, with no memory prefactor.
* `rowA_history_free_small_bare_coupling` — the Row-A completion predicate at
  every sufficiently small bare coupling, from the five channel majorants, the
  Gaussian window and the quartic debt **alone**: no drive, no Duhamel constant,
  no coefficient-to-state Lipschitz constant, no irrelevant state at all.

**Honest status.**  Row A is not closed and nothing is promoted.  This theorem
removes the memory hypotheses from the Row-A package *under the assumption*
that the literal shell data are scale-attached rather than bare-coupling
attached; whether the literal Bałaban shell coefficients are scale-attached in
this sense is precisely the identification still outstanding, and it is
hypothesised here (`hZfree` and the four channel-freeness hypotheses), not
proved.
-/
import RequestProject.YangMills.RowASmallBareCoupling

namespace YangMills

open Finset

/-- With an empty memory sector the total response mass is exactly the resummed
marginal weight: `σ = (C_dir/2)(u₀⁻³ + 1/(2 b u₀²))`. -/
theorem literalKernelMass_history_free (Cdir thmem u₀ bl : ℝ) :
    literalKernelMass Cdir 0 thmem u₀ bl
      = (Cdir / 2) * ((u₀ ^ 3)⁻¹ + 1 / (2 * bl * u₀ ^ 2)) := by
  rw [literalKernelMass]
  simp

/-- **Row A on the history-free fork.**  If the Gaussian shell coefficient and
the five channel data are attached to the scale rather than to the bare
coupling, then the Row-A completion predicate holds at every sufficiently small
bare coupling, with *no* memory hypothesis: the only inputs are the Cauchy and
spectral majorants of the channels, the two-sided Gaussian window, and the
quartic debt bound. -/
theorem rowA_history_free_small_bare_coupling
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir bZm bZp Cint ubase : ℝ}
    (hZfree : ∀ j p q, betaZ j p = betaZ j q)
    (hDfree : ∀ j p q, lamD j p = lamD j q) (hGfree : ∀ j p q, lamG j p = lamG j q)
    (hIfree : ∀ j p q, aI j p = aI j q) (hCfree : ∀ j p q, aC j p = aC j q)
    (hLfree : ∀ j p q, aL j p = aL j q)
    (hstruct : ∀ j p, ubase ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hth0 : 0 < theta) (hth : theta < 1) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hZl : ∀ j p, ubase ≤ p → bZm ≤ betaZ j p) (hZu : ∀ j p, ubase ≤ p → betaZ j p ≤ bZp)
    (hIntQ : ∀ j p, ubase ≤ p →
      |frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aC j p) (aL j p) N
        (couplingOf (shootingTrajectory bet p j))| ≤ Cint * couplingOf p ^ 4)
    (hCint : 0 ≤ Cint) (hbZm : 0 < bZm) (hubase : 0 < ubase) :
    ∃ U : ℝ, ubase ≤ U ∧ 1 ≤ U ∧
      ∀ u₀ : ℝ, U ≤ u₀ → ∀ (K : ℕ) (target : ℝ),
        u₀ + (bZp + quarticDebtTolerance Cint u₀) * K ≤ target →
        RowACompletion bet K target
          (bZm - quarticDebtTolerance Cint u₀) (bZp + quarticDebtTolerance Cint u₀)
          (target - (bZp + quarticDebtTolerance Cint u₀) * K)⁻¹ := by
  -- the irrelevant sector is a single trivial coordinate carrying the zero state
  have hhalf : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  refine rowA_small_bare_coupling (Op := Fin 1)
    (dim := fun _ => 5) (Nl := fun _ _ _ => 0) (rst := fun _ _ => 0)
    (Lcoef := 0) (Cmem := 0) (Cgen := 0) (L := 2) (delta := 1) (eta := 0)
    (Cdir := Cdir) (theta := theta) (rho := rho)
    hstruct hLd hLg hLd0 hLg0 hI hC hLc hAI hAC hAL hK hth0 hth hrho0 hrho1 hCdir
    hZl hZu hIntQ hCint (by norm_num) (fun _ => by norm_num)
    (fun _ _ _ _ => by simp) le_rfl (by rw [hhalf]; norm_num)
    (fun _ _ _ _ _ _ _ _ _ => by simp) le_rfl
    (fun _ _ _ _ => rfl) ?_ ?_ le_rfl ?_ le_rfl hbZm hubase
  · -- the zero state is a fixed point of the trivial renormalisation-group step
    intro j p _
    funext o
    simp [rgStep, blockScaling]
  · -- the shell coefficient does not depend on the bare coupling at all
    intro j p q g
    have hEq : literalShellAt betaZ lamD lamG aI aC aL N j p g
        = literalShellAt betaZ lamD lamG aI aC aL N j q g := by
      rw [literalShellAt, literalShellAt, hZfree j p q, hDfree j p q, hGfree j p q,
        hIfree j p q, hCfree j p q, hLfree j p q]
    rw [hEq, sub_self, abs_zero]
    simp
  · -- the memory domination hypothesis is vacuous when both sides vanish
    simp

/-! ## The boxed inequality, history-free -/

/-- **The literal cumulative beta map is `q`-Lipschitz with `q < 1`, history-free.**

With `𝓑_K(p) = Σ_{j<K} β_j(p)` the literal cumulative beta correction generated
by the bare inverse coupling `p`, and the shell data attached to the scale,

    |𝓑_K(p) − 𝓑_K(q)| ≤ q·|p − q|,    q = σ/(1−σ) < 1,

uniformly in the cutoff `K`, where `σ = (C_dir/2)(u₀⁻³ + 1/(2 b u₀²))` is the
resummed *direct* marginal weight alone.  The smallness hypothesis is the single
inequality `C_dir(1 + 1/(2b)) < u₀²`, i.e. a sufficiently small bare coupling;
no memory constant and no forgetting law appear. -/
theorem literal_cumulative_beta_contraction_history_free
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {bet betaZ : ℕ → ℝ → ℝ} {lamD : ℕ → ℝ → ι → ℝ} {lamG : ℕ → ℝ → κ → ℝ}
    {aI aC aL : ℕ → ℝ → ℕ → ℝ} {N : ℕ}
    {LamDet LamGauge theta AI AC AL Kmaj rho Cdir u₀ bl : ℝ}
    (hZfree : ∀ j p q, betaZ j p = betaZ j q)
    (hDfree : ∀ j p q, lamD j p = lamD j q) (hGfree : ∀ j p q, lamG j p = lamG j q)
    (hIfree : ∀ j p q, aI j p = aI j q) (hCfree : ∀ j p q, aC j p = aC j q)
    (hLfree : ∀ j p q, aL j p = aL j q)
    (hstruct : ∀ j p, u₀ ≤ p → bet j p
      = literalShellAt betaZ lamD lamG aI aC aL N j p
          (couplingOf (shootingTrajectory bet p j)))
    (hLd : ∀ j p i, |lamD j p i| ≤ LamDet) (hLg : ∀ j p i, |lamG j p i| ≤ LamGauge)
    (hLd0 : 0 ≤ LamDet) (hLg0 : 0 ≤ LamGauge)
    (hI : ∀ j p n, |aI j p n| ≤ AI * Kmaj ^ (n + 4))
    (hC : ∀ j p n, |aC j p n| ≤ AC * Kmaj ^ (n + 4))
    (hLc : ∀ j p n, |aL j p n| ≤ AL * Kmaj ^ (n + 4))
    (hAI : 0 ≤ AI) (hAC : 0 ≤ AC) (hAL : 0 ≤ AL) (hK : 0 ≤ Kmaj)
    (hGLd : couplingOf u₀ * LamDet ≤ theta) (hGLg : couplingOf u₀ * LamGauge ≤ theta)
    (hth : theta < 1) (hrho : Kmaj * couplingOf u₀ ≤ rho) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hCdir : analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho ≤ Cdir)
    (hu₀ : 1 ≤ u₀) (hbl : 0 < bl) (hlow : ∀ j p, u₀ ≤ p → bl ≤ bet j p)
    (hsmall : Cdir * (1 + 1 / (2 * bl)) < u₀ ^ 2) :
    (∀ (K : ℕ) (p q : ℝ), u₀ ≤ p → u₀ ≤ q →
        |∑ j ∈ range K, bet j p - ∑ j ∈ range K, bet j q|
          ≤ (literalKernelMass Cdir 0 0 u₀ bl
              / (1 - literalKernelMass Cdir 0 0 u₀ bl)) * |p - q|)
      ∧ literalKernelMass Cdir 0 0 u₀ bl
          / (1 - literalKernelMass Cdir 0 0 u₀ bl) < 1 := by
  have hCdir0 : 0 ≤ analyticDirectSensitivityBound (Fintype.card ι) (Fintype.card κ)
      LamDet LamGauge theta AI AC AL Kmaj rho :=
    analyticDirectSensitivityBound_nonneg hth hAI hAC hAL hrho1
  have hCd0 : 0 ≤ Cdir := le_trans hCdir0 hCdir
  have hu0 : 0 < u₀ := lt_of_lt_of_le one_pos hu₀
  have hsig : literalKernelMass Cdir 0 0 u₀ bl < 1 / 2 := by
    refine literal_sigma_lt_half hCd0 le_rfl (by norm_num) hbl hu₀ ?_
    simpa using hsmall
  refine literal_cumulative_beta_contraction hstruct hLd hLg hLd0 hLg0 hI hC hLc
    hAI hAC hAL hK hGLd hGLg hth hrho hrho0 hrho1 hCdir ?_ le_rfl le_rfl one_pos
    hu0 hbl hlow hsig
  intro j p q g _ _
  have hEq : literalShellAt betaZ lamD lamG aI aC aL N j p g
      = literalShellAt betaZ lamD lamG aI aC aL N j q g := by
    rw [literalShellAt, literalShellAt, hZfree j p q, hDfree j p q, hGfree j p q,
      hIfree j p q, hCfree j p q, hLfree j p q]
  rw [hEq, sub_self, abs_zero]
  simp

end YangMills
