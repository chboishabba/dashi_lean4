/-
# The finite near core as one scalar: the determinant taper and the local zero phase sum

`OffOrdinateCutoffCarrier` reduces the literal off-ordinate projective defect of a
single taper to a *finite* signed sum plus an explicit far remainder.  For a
three-taper observer the object that the Schur contradiction consumes is the vector

    𝔇_off(g, t, r) = (𝔇_off(g₀,t,r), 𝔇_off(g₁,t,r), 𝔇_off(g₂,t,r)) ∈ ℝ³ ,

and, after eliminating the two deterministic nuisance directions `n₁, n₂`, its
surviving energy.  `ThreeTaperSchurGram` shows that this energy is governed by one
scalar, the `3 × 3` determinant `det3(n₁, n₂, ·)` of the channel column.

This module carries out that scalarization on the *literal* carrier.  Writing
`c = n₁ × n₂` and

    q(u) = det3(n₁, n₂, (projTaper gⱼ r u)ⱼ) = ∑ⱼ cⱼ · projTaper gⱼ r u

for the **determinant taper**, and

    S(t, J; u) = ∑_{σ ∈ nearOffFinset t J} m_σ · cosh(a_σ u) · cos((b_σ − t) u)

for the **local zero phase sum** over the finite near carrier (`a_σ` the height,
`b_σ` the ordinate of `σ`), the results are:

* `cellDet_nearCell_eq_integral` — one zero's scalar cell response is
  `2 m_σ ∫ q(u) cosh(a_σ u) cos((b_σ − t)u) du`;
* `sum_cellDet_nearCell_eq_integral` — the whole finite near core is the *single*
  oscillatory integral `2 ∫ q(u) S(t,J;u) du`;
* `normSqP_elim2_nearVec_eq` — hence the surviving near energy is
  `4 (∫ q S)² / wedgeSq(n₁,n₂)`;
* `abs_det3_offVec_sub_det3_nearVec_le` and `normSqP_elim2_offVec_le` — the far
  remainder is transported into the same scalar coordinate, so the *entire*
  off-ordinate energy is bounded by `(|2 ∫ q S| + ‖c‖₁ · ½ C · farShellBound A |t| J)²`
  divided by the Gram determinant.

No vector-valued Gram algebra is left: the remaining analytic content is a bound for
the target-centred exponential sum `∫ q(u) S(t,J;u) du` over the finitely many zeros
with `|Im σ − t| < J`.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.ThreeTaperSchurGram
import Zeta23Bridge.OffOrdinateCutoffCarrier

noncomputable section

open scoped Real
open Zeta23 MeasureTheory

namespace Zeta23Bridge
namespace NearCoreDeterminantTaper

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurMargin
open Zeta23Bridge.ThreeTaperSchurGram
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.FarShellCutoffTailBound
open Zeta23Bridge.NearFarCarrierSplit
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-! ## 0. Integrability of the reflection-pair kernel -/

theorem integrable_reflectionPairWeight {p : ℝ → ℝ}
    (hp : Continuous p) (hpc : HasCompactSupport p) (a δ : ℝ) :
    Integrable (reflectionPairWeight p a δ) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · unfold reflectionPairWeight; fun_prop
  · have h : HasCompactSupport (fun u : ℝ => 4 * p u) := hpc.mul_left
    exact (h.mul_right).mul_right

/-- The literal reflection-pair response of a zero is the signed oscillatory integral
of the pair kernel. -/
theorem pairTerm_eq_integral {p : ℝ → ℝ}
    (hp : Continuous p) (hpc : HasCompactSupport p) (heven : ∀ u, p (-u) = p u)
    (t : ℝ) (ρ : Zeros) :
    pairTerm p t ρ
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
          * ∫ u : ℝ, reflectionPairWeight p (heightOf ρ) ((ρ : ℂ).im - t) u := by
  have h := zeroConeValue_add_reflect_eq_integral hp hpc heven t 0 ρ
  unfold pairTerm
  rw [h]
  simp

/-! ## 1. The determinant taper and the local zero phase sum -/

/-- The **determinant taper**: the single scalar taper obtained by contracting the
three projected tapers against the cross product of the two nuisance directions. -/
def detTaper (n₁ n₂ : Fin 3 → ℝ) (g : Fin 3 → (ℝ → ℝ)) (r : ℝ) : ℝ → ℝ :=
  fun u => ∑ j, cross3 n₁ n₂ j * projTaper (g j) r u

/-- The **local zero phase sum** of the finite near carrier at the target ordinate. -/
def localZeroPhaseSum (t : ℝ) (J : ℕ) : ℝ → ℝ :=
  fun u => ∑ σ ∈ nearOffFinset t J,
    ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
      * Real.cosh (heightOf (σ : Zeros) * u)
      * Real.cos ((((σ : Zeros) : ℂ).im - t) * u)

/-! ## 2. The three-taper channel columns -/

/-- The near cell of a single off-ordinate zero: one half of its symmetrized pair
response in each of the three tapers. -/
def nearCell (g : Fin 3 → (ℝ → ℝ)) (t r : ℝ) (σ : ((SameOrd t)ᶜ : Set Zeros)) : Fin 3 → ℝ :=
  fun j => (1 / 2 : ℝ) * offPairTerm (g j) t r σ

/-- The finite near-core channel column. -/
def nearVec (g : Fin 3 → (ℝ → ℝ)) (t r : ℝ) (J : ℕ) : Fin 3 → ℝ :=
  fun j => (1 / 2 : ℝ) * ∑ σ ∈ nearOffFinset t J, offPairTerm (g j) t r σ

/-- The literal off-ordinate channel column. -/
def offVec (g : Fin 3 → (ℝ → ℝ)) (t r : ℝ) : Fin 3 → ℝ :=
  fun j => offOrdProjectiveDefect (g j) t r

theorem nearVec_eq_sum (g : Fin 3 → (ℝ → ℝ)) (t r : ℝ) (J : ℕ) :
    nearVec g t r J = ∑ σ ∈ nearOffFinset t J, nearCell g t r σ := by
  funext j
  simp only [nearVec, nearCell, Finset.sum_apply, Finset.mul_sum]

/-! ## 3. One zero: the scalar cell response is one oscillatory integral -/

/-- **Scalarization of a single near cell.**  All three tapers share the same
reflection-pair factor, so third-slot linearity of the determinant collapses the
vector cell to a single integral against the determinant taper. -/
theorem cellDet_nearCell_eq_integral {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j, ∀ u, g j (-u) = g j u) (n₁ n₂ : Fin 3 → ℝ) (t r : ℝ)
    (σ : ((SameOrd t)ᶜ : Set Zeros)) :
    cellDet n₁ n₂ (nearCell g t r σ)
      = 2 * ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
          * ∫ u : ℝ, detTaper n₁ n₂ g r u
              * (Real.cosh (heightOf (σ : Zeros) * u)
                  * Real.cos ((((σ : Zeros) : ℂ).im - t) * u)) := by
  classical
  set a := heightOf (σ : Zeros)
  set δ := (((σ : Zeros) : ℂ).im - t)
  set m := ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
  have hcont : ∀ j, Continuous (projTaper (g j) r) := fun j =>
    projTaper_continuous (hgs j) r
  have hsupp : ∀ j, HasCompactSupport (projTaper (g j) r) := fun j =>
    projTaper_hasCompactSupport (hgc j) r
  have hpeven : ∀ j, ∀ u, projTaper (g j) r (-u) = projTaper (g j) r u := fun j =>
    projTaper_even (heven j) r
  -- each coordinate is `m` times an integral
  have hcoord : ∀ j, nearCell g t r σ j
      = (1 / 2 : ℝ) * (m * ∫ u : ℝ, reflectionPairWeight (projTaper (g j) r) a δ u) := by
    intro j
    unfold nearCell
    rw [offPairTerm_eq_pairTerm,
      pairTerm_eq_integral (hcont j) (hsupp j) (hpeven j) t (σ : Zeros)]
  have hint : ∀ j, Integrable
      (fun u : ℝ => cross3 n₁ n₂ j * reflectionPairWeight (projTaper (g j) r) a δ u) :=
    fun j => (integrable_reflectionPairWeight (hcont j) (hsupp j) a δ).const_mul _
  have hswap :
      ∑ j, cross3 n₁ n₂ j * ∫ u : ℝ, reflectionPairWeight (projTaper (g j) r) a δ u
        = ∫ u : ℝ, ∑ j,
            cross3 n₁ n₂ j * reflectionPairWeight (projTaper (g j) r) a δ u := by
    rw [integral_finsetSum _ (fun j _ => hint j)]
    exact Finset.sum_congr rfl (fun j _ => (integral_const_mul _ _).symm)
  have hpoint : ∀ u : ℝ,
      ∑ j, cross3 n₁ n₂ j * reflectionPairWeight (projTaper (g j) r) a δ u
        = 4 * (detTaper n₁ n₂ g r u * (Real.cosh (a * u) * Real.cos (δ * u))) := by
    intro u
    unfold detTaper reflectionPairWeight
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hdet : cellDet n₁ n₂ (nearCell g t r σ)
      = ∑ j, cross3 n₁ n₂ j * nearCell g t r σ j := by
    unfold cellDet
    rw [det3_eq_dotP_cross3]
    rfl
  rw [hdet]
  have : ∑ j, cross3 n₁ n₂ j * nearCell g t r σ j
      = (1 / 2 : ℝ) * m *
        ∑ j, cross3 n₁ n₂ j * ∫ u : ℝ, reflectionPairWeight (projTaper (g j) r) a δ u := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcoord j]; ring
  rw [this, hswap]
  have hcongr : (∫ u : ℝ, ∑ j,
        cross3 n₁ n₂ j * reflectionPairWeight (projTaper (g j) r) a δ u)
      = ∫ u : ℝ, 4 * (detTaper n₁ n₂ g r u * (Real.cosh (a * u) * Real.cos (δ * u))) := by
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [hcongr, integral_const_mul]
  ring

/-! ## 4. The whole finite core: one oscillatory integral against the phase sum -/

theorem integrable_detTaper_phase {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (n₁ n₂ : Fin 3 → ℝ) (r a δ : ℝ) :
    Integrable (fun u : ℝ => detTaper n₁ n₂ g r u
      * (Real.cosh (a * u) * Real.cos (δ * u))) := by
  have hterm : ∀ j : Fin 3, Integrable (fun u : ℝ =>
      cross3 n₁ n₂ j * projTaper (g j) r u * (Real.cosh (a * u) * Real.cos (δ * u))) := by
    intro j
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have := projTaper_continuous (hgs j) r
      fun_prop
    · have h : HasCompactSupport (fun u : ℝ => cross3 n₁ n₂ j * projTaper (g j) r u) :=
        (projTaper_hasCompactSupport (hgc j) r).mul_left
      exact h.mul_right
  have hrw : (fun u : ℝ => detTaper n₁ n₂ g r u
        * (Real.cosh (a * u) * Real.cos (δ * u)))
      = fun u : ℝ => ∑ j, cross3 n₁ n₂ j * projTaper (g j) r u
          * (Real.cosh (a * u) * Real.cos (δ * u)) := by
    funext u
    unfold detTaper
    rw [Finset.sum_mul]
  rw [hrw]
  exact integrable_finsetSum _ (fun j _ => hterm j)

/-- **The finite near core is a single target-centred oscillatory integral.**  Summing
the scalarized cells over the finite near carrier moves the sum inside the integral:
what remains is the determinant taper tested against the local zero phase sum. -/
theorem sum_cellDet_nearCell_eq_integral {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j, ∀ u, g j (-u) = g j u) (n₁ n₂ : Fin 3 → ℝ) (t r : ℝ) (J : ℕ) :
    ∑ σ ∈ nearOffFinset t J, cellDet n₁ n₂ (nearCell g t r σ)
      = 2 * ∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u := by
  classical
  have hcell : ∀ σ ∈ nearOffFinset t J, cellDet n₁ n₂ (nearCell g t r σ)
      = 2 * ∫ u : ℝ, ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
          * (detTaper n₁ n₂ g r u
              * (Real.cosh (heightOf (σ : Zeros) * u)
                  * Real.cos ((((σ : Zeros) : ℂ).im - t) * u))) := by
    intro σ _
    rw [cellDet_nearCell_eq_integral hgs hgc heven n₁ n₂ t r σ, integral_const_mul]
    ring
  have hint : ∀ σ ∈ nearOffFinset t J, Integrable (fun u : ℝ =>
      ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
        * (detTaper n₁ n₂ g r u
            * (Real.cosh (heightOf (σ : Zeros) * u)
                * Real.cos ((((σ : Zeros) : ℂ).im - t) * u)))) := by
    intro σ _
    exact (integrable_detTaper_phase hgs hgc n₁ n₂ r (heightOf (σ : Zeros))
      ((((σ : Zeros) : ℂ).im - t))).const_mul _
  rw [Finset.sum_congr rfl hcell, ← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [localZeroPhaseSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

/-! ## 5. The surviving near energy, and the transported far remainder -/

/-- **The surviving finite near energy is one scalar squared.** -/
theorem normSqP_elim2_nearVec_eq {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j, ∀ u, g j (-u) = g j u) (n₁ n₂ : Fin 3 → ℝ)
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) (t r : ℝ) (J : ℕ) :
    normSqP (elim2 n₁ n₂ (nearVec g t r J))
      = (2 * ∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u) ^ 2
          / wedgeSq n₁ n₂ := by
  classical
  rw [nearVec_eq_sum, normSqP_elim2_sum_eq_sq_sum_cellDet_div n₁ n₂ _ _ hn₁ hn₂,
    sum_cellDet_nearCell_eq_integral hgs hgc heven n₁ n₂ t r J]

/-- The scalar determinant of the literal off-ordinate column differs from that of the
finite near core by at most the `ℓ¹` norm of the cross product times the explicit far
remainder. -/
theorem abs_det3_offVec_sub_det3_nearVec_le {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, ContDiff ℝ 2 (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j, ∀ u, g j (-u) = g j u) (n₁ n₂ : Fin 3 → ℝ) (t r : ℝ) {A C : ℝ}
    (hA1 : 1 ≤ A) (hC0 : 0 ≤ C)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (hC : ∀ j, ∀ ρ : Zeros, pairWeightCurvature (projTaper (g j) r) (heightOf ρ) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) :
    |det3 n₁ n₂ (offVec g t r) - det3 n₁ n₂ (nearVec g t r J)|
      ≤ (∑ j, |cross3 n₁ n₂ j|) * ((1 / 2 : ℝ) * (C * farShellBound A |t| J)) := by
  classical
  have hcoord : ∀ j : Fin 3,
      |offVec g t r j - nearVec g t r J j| ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J) := by
    intro j
    exact abs_offOrdProjectiveDefect_sub_nearCore_le (hgs j) (hgc j) (heven j) t r
      hA1 hC0 hloc (hC j) J hJ
  have hdiff : det3 n₁ n₂ (offVec g t r) - det3 n₁ n₂ (nearVec g t r J)
      = ∑ j, cross3 n₁ n₂ j * (offVec g t r j - nearVec g t r J j) := by
    simp only [det3_eq_dotP_cross3, dotP, Fin.sum_univ_three]
    ring
  rw [hdiff]
  calc |∑ j, cross3 n₁ n₂ j * (offVec g t r j - nearVec g t r J j)|
      ≤ ∑ j, |cross3 n₁ n₂ j * (offVec g t r j - nearVec g t r J j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |cross3 n₁ n₂ j| * ((1 / 2 : ℝ) * (C * farShellBound A |t| J)) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
    _ = (∑ j, |cross3 n₁ n₂ j|) * ((1 / 2 : ℝ) * (C * farShellBound A |t| J)) := by
        rw [Finset.sum_mul]

/-- **The whole off-ordinate surviving energy is controlled by the single scalar
`∫ q · S`.**  Every remaining analytic obligation of the off-ordinate lane is a bound
for that target-centred exponential sum over the finitely many zeros with
`|Im σ − t| < J`, plus the explicit far remainder. -/
theorem normSqP_elim2_offVec_le {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, ContDiff ℝ 2 (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j, ∀ u, g j (-u) = g j u) (n₁ n₂ : Fin 3 → ℝ)
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) (t r : ℝ) {A C : ℝ}
    (hA1 : 1 ≤ A) (hC0 : 0 ≤ C)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (hC : ∀ j, ∀ ρ : Zeros, pairWeightCurvature (projTaper (g j) r) (heightOf ρ) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) :
    normSqP (elim2 n₁ n₂ (offVec g t r))
      ≤ (|2 * ∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u|
            + (∑ j, |cross3 n₁ n₂ j|) * ((1 / 2 : ℝ) * (C * farShellBound A |t| J))) ^ 2
          / wedgeSq n₁ n₂ := by
  classical
  have hcont : ∀ j, Continuous (g j) := fun j => (hgs j).continuous
  have hw : 0 < wedgeSq n₁ n₂ := by
    have h := wedgeSq_eq_normSqP_mul_transverse hn₁ n₂
    have h1 : 0 < normSqP n₁ := normSqP_pos_of_ne_zero hn₁
    have h2 : 0 < normSqP (perp2 n₁ n₂) := normSqP_pos_of_ne_zero hn₂
    rw [h]; exact mul_pos h1 h2
  have hnearDet : det3 n₁ n₂ (nearVec g t r J)
      = 2 * ∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u := by
    rw [nearVec_eq_sum, det3_sum_right]
    exact sum_cellDet_nearCell_eq_integral hcont hgc heven n₁ n₂ t r J
  have hsplit := abs_det3_offVec_sub_det3_nearVec_le hgs hgc heven n₁ n₂ t r
    hA1 hC0 hloc hC J hJ
  rw [hnearDet] at hsplit
  set S := 2 * ∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u with hS
  set E := (∑ j, |cross3 n₁ n₂ j|) * ((1 / 2 : ℝ) * (C * farShellBound A |t| J)) with hE
  have habs : |det3 n₁ n₂ (offVec g t r)| ≤ |S| + E := by
    calc |det3 n₁ n₂ (offVec g t r)|
        = |(det3 n₁ n₂ (offVec g t r) - S) + S| := by ring_nf
      _ ≤ |det3 n₁ n₂ (offVec g t r) - S| + |S| := abs_add_le _ _
      _ ≤ E + |S| := by linarith [hsplit]
      _ = |S| + E := by ring
  have hEnonneg : 0 ≤ E := by
    have h1 : (0 : ℝ) ≤ ∑ j, |cross3 n₁ n₂ j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have h2 : 0 ≤ farShellBound A |t| J := by
      have := tailMajorant_nonneg (A := A) (a := |t|) (x := (J : ℝ))
        (by linarith) (abs_nonneg t) (Nat.cast_nonneg J)
      unfold farShellBound
      linarith
    have : 0 ≤ (1 / 2 : ℝ) * (C * farShellBound A |t| J) := by positivity
    exact mul_nonneg h1 this
  rw [normSqP_elim2_eq_det3_sq_div n₁ n₂ _ hn₁ hn₂]
  refine div_le_div_of_nonneg_right ?_ hw.le
  have hsq : det3 n₁ n₂ (offVec g t r) ^ 2 ≤ (|S| + E) ^ 2 := by
    have h0 : |det3 n₁ n₂ (offVec g t r)| ^ 2 = det3 n₁ n₂ (offVec g t r) ^ 2 :=
      sq_abs _
    nlinarith [abs_nonneg (det3 n₁ n₂ (offVec g t r)), habs, hEnonneg, abs_nonneg S]
  exact hsq

/-! ## 6. The scalar frontier quantity, zero by zero -/

/-- The determinant-taper response of a single reflection pair: the cosine transform of
the determinant taper at the target-relative ordinate gap, weighted by `cosh` of the
height. -/
def zeroDetResponse (n₁ n₂ : Fin 3 → ℝ) (g : Fin 3 → (ℝ → ℝ)) (r a δ : ℝ) : ℝ :=
  ∫ u : ℝ, detTaper n₁ n₂ g r u * (Real.cosh (a * u) * Real.cos (δ * u))

/-- **The frontier scalar as a finite exponential sum over the near zeros.** -/
theorem integral_detTaper_localZeroPhaseSum_eq_sum {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (n₁ n₂ : Fin 3 → ℝ) (t r : ℝ) (J : ℕ) :
    (∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u)
      = ∑ σ ∈ nearOffFinset t J,
          ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
            * zeroDetResponse n₁ n₂ g r (heightOf (σ : Zeros))
                ((((σ : Zeros) : ℂ).im - t)) := by
  classical
  have hint : ∀ σ ∈ nearOffFinset t J, Integrable (fun u : ℝ =>
      ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
        * (detTaper n₁ n₂ g r u
            * (Real.cosh (heightOf (σ : Zeros) * u)
                * Real.cos ((((σ : Zeros) : ℂ).im - t) * u)))) := by
    intro σ _
    exact (integrable_detTaper_phase hgs hgc n₁ n₂ r (heightOf (σ : Zeros))
      ((((σ : Zeros) : ℂ).im - t))).const_mul _
  have hpoint : (fun u : ℝ => detTaper n₁ n₂ g r u * localZeroPhaseSum t J u)
      = fun u : ℝ => ∑ σ ∈ nearOffFinset t J,
          ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
            * (detTaper n₁ n₂ g r u
                * (Real.cosh (heightOf (σ : Zeros) * u)
                    * Real.cos ((((σ : Zeros) : ℂ).im - t) * u))) := by
    funext u
    simp only [localZeroPhaseSum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by ring)
  rw [hpoint, integral_finsetSum _ hint]
  exact Finset.sum_congr rfl (fun σ _ => integral_const_mul _ _)

/-! ## 7. The consumer: what a scalar bound would buy -/

/-- **The reduction, in consumer form.**  Any bound on the single scalar
`2 ∫ q · S` — the target-centred exponential sum over the finitely many zeros with
`|Im σ − t| < J` — together with the explicit far remainder, bounds the whole surviving
off-ordinate energy strictly below a prescribed margin.  This is a reduction: the
hypothesis `hB` is precisely the analytic obligation that remains, and nothing here
asserts it. -/
theorem normSqP_elim2_offVec_lt_of_scalar_bound {g : Fin 3 → (ℝ → ℝ)}
    (hgs : ∀ j, ContDiff ℝ 2 (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j, ∀ u, g j (-u) = g j u) (n₁ n₂ : Fin 3 → ℝ)
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) (t r : ℝ) {A C : ℝ}
    (hA1 : 1 ≤ A) (hC0 : 0 ≤ C)
    (hloc : ∀ τ : ℝ, ((zetaZeroConfig).N τ (τ + 1) : ℝ) ≤ A * Real.log (|τ| + 3))
    (hC : ∀ j, ∀ ρ : Zeros, pairWeightCurvature (projTaper (g j) r) (heightOf ρ) ≤ C)
    (J : ℕ) (hJ : 1 ≤ J) {M : ℝ}
    (hB : (|2 * ∫ u : ℝ, detTaper n₁ n₂ g r u * localZeroPhaseSum t J u|
            + (∑ j, |cross3 n₁ n₂ j|) * ((1 / 2 : ℝ) * (C * farShellBound A |t| J))) ^ 2
          < wedgeSq n₁ n₂ * M) :
    normSqP (elim2 n₁ n₂ (offVec g t r)) < M := by
  have hw : 0 < wedgeSq n₁ n₂ := by
    have h := wedgeSq_eq_normSqP_mul_transverse hn₁ n₂
    have h1 : 0 < normSqP n₁ := normSqP_pos_of_ne_zero hn₁
    have h2 : 0 < normSqP (perp2 n₁ n₂) := normSqP_pos_of_ne_zero hn₂
    rw [h]; exact mul_pos h1 h2
  have hle := normSqP_elim2_offVec_le hgs hgc heven n₁ n₂ hn₁ hn₂ t r hA1 hC0 hloc hC J hJ
  refine lt_of_le_of_lt hle ?_
  rw [div_lt_iff₀ hw]
  linarith [hB]

/-- **The scalar frontier inherits the balance no-go.**  If the cluster column agrees
with the literal off-ordinate column modulo the two deterministic nuisance columns —
which is exactly what the literal projective balance supplies — then the surviving
cluster margin *is* the surviving off-ordinate energy, so no scalar bound whatsoever can
make the latter strictly smaller.  Any route to a contradiction must therefore break the
balance, not sharpen the estimate. -/
theorem not_normSqP_elim2_offVec_lt_of_balance {g : Fin 3 → (ℝ → ℝ)}
    {n₁ n₂ cluster : Fin 3 → ℝ} (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) (t r : ℝ)
    (hbalance : cluster = offVec g t r + n₁ + n₂) :
    ¬ normSqP (elim2 n₁ n₂ (offVec g t r)) < normSqP (elim2 n₁ n₂ cluster) := by
  rw [normSqP_elim2_eq_of_balance hn₁ hn₂ hbalance]
  exact lt_irrefl _

end NearCoreDeterminantTaper
end Zeta23Bridge
