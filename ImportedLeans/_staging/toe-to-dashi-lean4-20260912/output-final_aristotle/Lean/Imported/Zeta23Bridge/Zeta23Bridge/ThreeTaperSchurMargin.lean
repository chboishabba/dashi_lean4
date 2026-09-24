/-
# The exact surviving margin after two-nuisance elimination

`ThreeTaperSchurCore` proves the *qualitative* survival criterion

    det3 n₁ n₂ t ≠ 0  ⟹  elim2 n₁ n₂ t ≠ 0,

which is enough to know that the target is not annihilated, but not enough to
feed the final contradiction compiler: that compiler consumes a *number*
`margin ≤ ‖elim2 n₁ n₂ t‖²`, and so far every such margin had to be assumed.

This module removes that assumption by computing the surviving energy exactly:

    ‖elim2 n₁ n₂ t‖² = det3(n₁, n₂, t)² / wedgeSq(n₁, n₂).

The proof is exact three-dimensional linear algebra.  Writing `c = n₁ × n₂`:

* `det3 n₁ n₂ w = ⟪c, w⟫`                                    (`det3_eq_dotP_cross3`)
* `‖c‖² = wedgeSq n₁ n₂`                                     (`normSqP_cross3`)
* `(a × b) × w = ⟪a,w⟫ • b − ⟪b,w⟫ • a`                       (`cross3_cross3_left`)
* Lagrange: `⟪u,v⟫² + ‖u × v‖² = ‖u‖²‖v‖²`                    (`lagrange_identity`)

Since `elim2 n₁ n₂ t` is orthogonal to both nuisance directions, the double
cross product vanishes on it, so Cauchy–Schwarz against `c` is an equality —
which is precisely the displayed formula.

Two consequences are recorded for the analytic lane.

* `normSqP_elim2_lower_bound`: an explicit *computable* floor for the surviving
  cluster energy, in terms of the 3×3 determinant of the three channel columns
  (pole, Gamma, cluster) and the Gram determinant of the deterministic pair.
* `false_of_normSqP_lt_det3_sq_div_wedgeSq`: the endpoint in the form the
  frontier actually needs — because the elimination is a contraction, it is
  enough to bound the *raw* (unprojected) far channel by that same explicit
  determinant ratio.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.ThreeTaperSchurCore

noncomputable section

namespace Zeta23Bridge
namespace ThreeTaperSchurMargin

open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurCore

/-! ## The three-dimensional cross product and its two exact identities -/

/-- The cross product on the three-taper channel space. -/
def cross3 (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

theorem det3_eq_dotP_cross3 (u v w : Fin 3 → ℝ) :
    det3 u v w = dotP (cross3 u v) w := by
  simp [det3, dotP, cross3, Fin.sum_univ_three]
  ring

theorem dotP_cross3_left (u v : Fin 3 → ℝ) : dotP u (cross3 u v) = 0 := by
  simp [dotP, cross3, Fin.sum_univ_three]
  ring

theorem dotP_cross3_right (u v : Fin 3 → ℝ) : dotP v (cross3 u v) = 0 := by
  simp [dotP, cross3, Fin.sum_univ_three]
  ring

/-- Lagrange's identity. -/
theorem lagrange_identity (u v : Fin 3 → ℝ) :
    dotP u v ^ 2 + normSqP (cross3 u v) = normSqP u * normSqP v := by
  simp [dotP, normSqP, cross3, Fin.sum_univ_three]
  ring

theorem normSqP_cross3 (u v : Fin 3 → ℝ) :
    normSqP (cross3 u v) = wedgeSq u v := by
  have h := lagrange_identity u v
  unfold wedgeSq
  linarith

/-- The `bac − cab` expansion of the iterated cross product. -/
theorem cross3_cross3_left (a b w : Fin 3 → ℝ) :
    cross3 (cross3 a b) w = (dotP a w) • b - (dotP b w) • a := by
  funext i
  fin_cases i <;>
    simp [cross3, dotP, Fin.sum_univ_three] <;> ring

/-- A vector orthogonal to both factors is parallel to the cross product, so
Cauchy–Schwarz against it is an equality. -/
theorem dotP_cross3_sq_of_orthogonal {a b w : Fin 3 → ℝ}
    (ha : dotP a w = 0) (hb : dotP b w = 0) :
    dotP (cross3 a b) w ^ 2 = wedgeSq a b * normSqP w := by
  have hzero : cross3 (cross3 a b) w = 0 := by
    rw [cross3_cross3_left, ha, hb]
    simp
  have hlag := lagrange_identity (cross3 a b) w
  rw [hzero] at hlag
  have h0 : normSqP (0 : Fin 3 → ℝ) = 0 := by simp [normSqP, dotP]
  rw [h0, normSqP_cross3] at hlag
  linarith

/-! ## `elim2` is orthogonal to both nuisance directions -/

/-- Expansion of a dot product against a transverse component. -/
theorem dotP_transverseComp_left (n m y : Fin 3 → ℝ) :
    dotP n (transverseComp m y) = dotP n y - (dotP m y / normSqP m) * dotP n m := by
  unfold transverseComp
  rw [dotP_sub_right, dotP_smul_right]

theorem dotP_nuisance_one_elim2 (n₁ n₂ x : Fin 3 → ℝ) :
    dotP n₁ (elim2 n₁ n₂ x) = 0 := by
  have h1 : dotP n₁ (transverseComp n₁ x) = 0 := dotP_transverseComp n₁ x
  have h2 : dotP n₁ (perp2 n₁ n₂) = 0 := dotP_transverseComp n₁ n₂
  show dotP n₁ (transverseComp (perp2 n₁ n₂) (transverseComp n₁ x)) = 0
  rw [dotP_transverseComp_left, h1, h2]
  ring

theorem dotP_nuisance_two_elim2 (n₁ n₂ x : Fin 3 → ℝ) :
    dotP (perp2 n₁ n₂) (elim2 n₁ n₂ x) = 0 :=
  dotP_transverseComp (perp2 n₁ n₂) (transverseComp n₁ x)

theorem dotP_second_nuisance_elim2 (n₁ n₂ x : Fin 3 → ℝ) :
    dotP n₂ (elim2 n₁ n₂ x) = 0 := by
  have hexp : dotP (perp2 n₁ n₂) (elim2 n₁ n₂ x)
      = dotP n₂ (elim2 n₁ n₂ x)
        - (dotP n₁ n₂ / normSqP n₁) * dotP n₁ (elim2 n₁ n₂ x) := by
    unfold perp2
    rw [dotP_comm, dotP_transverseComp_left, dotP_comm (elim2 n₁ n₂ x) n₂,
      dotP_comm (elim2 n₁ n₂ x) n₁]
  rw [dotP_nuisance_two_elim2, dotP_nuisance_one_elim2] at hexp
  linarith

/-! ## The exact margin -/

/-- The determinant is unchanged by the elimination: `elim2` only subtracts a
combination of the two nuisance directions. -/
theorem det3_elim2 (n₁ n₂ t : Fin 3 → ℝ) :
    det3 n₁ n₂ (elim2 n₁ n₂ t) = det3 n₁ n₂ t := by
  rw [elim2_eq_sub]
  simp only [det3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The exact surviving energy.**  After eliminating the two deterministic
nuisance directions from the three-taper channel, the energy that survives is
the squared `3 × 3` determinant of the three columns divided by the Gram
determinant of the nuisance pair. -/
theorem normSqP_elim2_mul_wedgeSq (n₁ n₂ t : Fin 3 → ℝ) :
    normSqP (elim2 n₁ n₂ t) * wedgeSq n₁ n₂ = det3 n₁ n₂ t ^ 2 := by
  have horth1 : dotP n₁ (elim2 n₁ n₂ t) = 0 := dotP_nuisance_one_elim2 n₁ n₂ t
  have horth2 : dotP n₂ (elim2 n₁ n₂ t) = 0 := dotP_second_nuisance_elim2 n₁ n₂ t
  have hkey := dotP_cross3_sq_of_orthogonal horth1 horth2
  rw [← det3_eq_dotP_cross3, det3_elim2] at hkey
  linarith

/-- The same identity in quotient form. -/
theorem normSqP_elim2_eq_det3_sq_div (n₁ n₂ t : Fin 3 → ℝ)
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) :
    normSqP (elim2 n₁ n₂ t) = det3 n₁ n₂ t ^ 2 / wedgeSq n₁ n₂ := by
  have hw : 0 < wedgeSq n₁ n₂ := by
    have h := wedgeSq_eq_normSqP_mul_transverse hn₁ n₂
    have h1 : 0 < normSqP n₁ := normSqP_pos_of_ne_zero hn₁
    have h2 : 0 < normSqP (perp2 n₁ n₂) := normSqP_pos_of_ne_zero hn₂
    rw [h]
    exact mul_pos h1 h2
  field_simp
  exact normSqP_elim2_mul_wedgeSq n₁ n₂ t

/-- **Computable floor for the surviving cluster energy.**  Every quantity on the
right-hand side is a finite algebraic expression in the three channel columns. -/
theorem normSqP_elim2_lower_bound (n₁ n₂ t : Fin 3 → ℝ)
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0) (m : ℝ)
    (hm : m ≤ det3 n₁ n₂ t ^ 2 / wedgeSq n₁ n₂) :
    m ≤ normSqP (elim2 n₁ n₂ t) := by
  rw [normSqP_elim2_eq_det3_sq_div n₁ n₂ t hn₁ hn₂]
  exact hm

/-! ## A checkable rank-two gate for the deterministic nuisance pair -/

/-- Positivity of the Gram determinant of the nuisance pair is exactly the
side condition the elimination needs. -/
theorem nuisance_pair_of_wedgeSq_pos {n₁ n₂ : Fin 3 → ℝ} (h : 0 < wedgeSq n₁ n₂) :
    n₁ ≠ 0 ∧ perp2 n₁ n₂ ≠ 0 := by
  have hn₁ : n₁ ≠ 0 := by
    intro hz
    rw [hz] at h
    simp [wedgeSq, normSqP, dotP] at h
  refine ⟨hn₁, ?_⟩
  intro hz
  have hfac := wedgeSq_eq_normSqP_mul_transverse hn₁ n₂
  rw [← perp2, hz] at hfac
  have h0 : normSqP (0 : Fin 3 → ℝ) = 0 := by simp [normSqP, dotP]
  rw [h0, mul_zero] at hfac
  linarith

/-- If the cross product vanishes then every `2 × 2` minor of the pair vanishes. -/
theorem minor_eq_zero_of_cross3_eq_zero {n₁ n₂ : Fin 3 → ℝ}
    (hzero : cross3 n₁ n₂ = 0) (i j : Fin 3) :
    n₁ i * n₂ j - n₁ j * n₂ i = 0 := by
  have h0 : n₁ 1 * n₂ 2 - n₁ 2 * n₂ 1 = 0 := by
    have := congrFun hzero 0; simpa [cross3] using this
  have h1 : n₁ 2 * n₂ 0 - n₁ 0 * n₂ 2 = 0 := by
    have := congrFun hzero 1; simpa [cross3] using this
  have h2 : n₁ 0 * n₂ 1 - n₁ 1 * n₂ 0 = 0 := by
    have := congrFun hzero 2; simpa [cross3] using this
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

/-- **A single nonvanishing `2 × 2` minor certifies the whole rank-two gate.**
This is the form in which the three-taper construction can discharge the two
side conditions of the exact elimination: exhibit two tapers on which the pole
and Gamma responses are not proportional. -/
theorem nuisance_pair_of_minor_ne_zero {n₁ n₂ : Fin 3 → ℝ}
    (i j : Fin 3) (h : n₁ i * n₂ j - n₁ j * n₂ i ≠ 0) :
    n₁ ≠ 0 ∧ perp2 n₁ n₂ ≠ 0 := by
  refine nuisance_pair_of_wedgeSq_pos ?_
  rw [← normSqP_cross3]
  refine lt_of_le_of_ne (normSqP_nonneg _) (fun hEq => ?_)
  exact h (minor_eq_zero_of_cross3_eq_zero
    ((normSqP_eq_zero_iff _).mp hEq.symm) i j)

/-! ## What the determinant algebra can and cannot buy -/

/-- Adding the two nuisance columns does not move the determinant. -/
theorem det3_add_nuisances (n₁ n₂ x : Fin 3 → ℝ) :
    det3 n₁ n₂ (x + n₁ + n₂) = det3 n₁ n₂ x := by
  simp only [det3, Pi.add_apply]
  ring

/-- **A sharp bookkeeping fact, stated so that it cannot be assumed away.**  Once
the literal projective balance `cluster = far + pole + Gamma` is in force, the
surviving cluster determinant *is* the far determinant.  Consequently the
"surviving cluster margin" and the "projected far tail" are literally the same
real number.  No further cancellation is available from the three-taper
determinant algebra: the endpoint can only be closed by an independent lower
bound for that number coming from the off-line target, together with an upper
bound coming from the zero-tail estimate. -/
theorem det3_eq_of_balance {n₁ n₂ cluster far : Fin 3 → ℝ}
    (hbalance : cluster = far + n₁ + n₂) :
    det3 n₁ n₂ cluster = det3 n₁ n₂ far := by
  rw [hbalance, det3_add_nuisances]

theorem normSqP_elim2_eq_of_balance {n₁ n₂ cluster far : Fin 3 → ℝ}
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0)
    (hbalance : cluster = far + n₁ + n₂) :
    normSqP (elim2 n₁ n₂ cluster) = normSqP (elim2 n₁ n₂ far) := by
  rw [normSqP_elim2_eq_det3_sq_div n₁ n₂ cluster hn₁ hn₂,
    normSqP_elim2_eq_det3_sq_div n₁ n₂ far hn₁ hn₂, det3_eq_of_balance hbalance]

/-- **The endpoint in the form the frontier needs.**  Suppose the cluster column
and the far column agree modulo the two deterministic nuisance columns — which is
exactly what the literal projective balance supplies.  Then it suffices to bound
the *raw* far column, before any projection, by the explicit determinant ratio of
the cluster column: the elimination can only shrink the far column, while the
cluster column keeps exactly the displayed energy. -/
theorem false_of_normSqP_lt_det3_sq_div_wedgeSq {n₁ n₂ cluster far : Fin 3 → ℝ}
    (hn₁ : n₁ ≠ 0) (hn₂ : perp2 n₁ n₂ ≠ 0)
    (hbalance : cluster = far + n₁ + n₂)
    (hfar : normSqP far < det3 n₁ n₂ cluster ^ 2 / wedgeSq n₁ n₂) : False := by
  have hsurv : normSqP (elim2 n₁ n₂ cluster) = det3 n₁ n₂ cluster ^ 2 / wedgeSq n₁ n₂ :=
    normSqP_elim2_eq_det3_sq_div n₁ n₂ cluster hn₁ hn₂
  have hreorder : cluster = n₁ + n₂ + far := by
    rw [hbalance]; funext i; simp [Pi.add_apply]; ring
  have heq : elim2 n₁ n₂ cluster = elim2 n₁ n₂ far := by
    rw [hreorder]
    exact elim2_add_nuisance hn₁ hn₂ far
  have hcontr : normSqP (elim2 n₁ n₂ far) ≤ normSqP far := by
    unfold elim2
    have h1 : normSqP (transverseComp (perp2 n₁ n₂) (transverseComp n₁ far))
        ≤ normSqP (transverseComp n₁ far) := by
      rw [normSqP_transverseComp hn₂]
      unfold schur
      have hq : 0 ≤ dotP (perp2 n₁ n₂) (transverseComp n₁ far) ^ 2
          / normSqP (perp2 n₁ n₂) :=
        div_nonneg (sq_nonneg _) (le_of_lt (normSqP_pos_of_ne_zero hn₂))
      linarith
    have h2 : normSqP (transverseComp n₁ far) ≤ normSqP far := by
      rw [normSqP_transverseComp hn₁]
      unfold schur
      have hq : 0 ≤ dotP n₁ far ^ 2 / normSqP n₁ :=
        div_nonneg (sq_nonneg _) (le_of_lt (normSqP_pos_of_ne_zero hn₁))
      linarith
    exact le_trans h1 h2
  rw [heq] at hsurv
  linarith

end ThreeTaperSchurMargin
end Zeta23Bridge
