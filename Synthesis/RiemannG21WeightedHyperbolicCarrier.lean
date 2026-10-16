import Mathlib.Tactic
import Synthesis.RiemannG21ContinuumMomentSymmetrization
import Synthesis.RiemannG21AtomicHyperbolicTP2

/-!
# G21 weighted hyperbolic symmetrized carriers

This specializes the exact continuum symmetrization carrier to the two literal
G21 height kernels.  For score `q(u)=u^2` and a common taper weight `w`, the
odd carrier factors as

  `(v^2-u^2) * w(u)w(v)
     * [sinh(a u)sinh(p v)-sinh(a v)sinh(p u)]`,

and likewise with `cosh` in the even sector.

On the positive support quadrant, the score difference and strict TP2 minor
have the same sign.  Therefore a nonnegative taper makes the carrier globally
nonnegative; on every ordered pair `0<u<v` where both taper weights are
strictly positive the carrier is strictly positive.

This pays the pointwise sign layer.  The remaining literal-continuum debt is
measure/integrability plus a positive-measure taper plateau.
-/

noncomputable section

namespace Synthesis

/-- Factored odd/sinh symmetrized carrier. -/
def oddWeightedSymmCarrier
    (w : ℝ → ℝ) (a p u v : ℝ) : ℝ :=
  (v^2 - u^2) * (w u * w v) *
    (Real.sinh (a*u) * Real.sinh (p*v)
      - Real.sinh (a*v) * Real.sinh (p*u))

/-- Factored even/cosh symmetrized carrier. -/
def evenWeightedSymmCarrier
    (w : ℝ → ℝ) (a p u v : ℝ) : ℝ :=
  (v^2 - u^2) * (w u * w v) *
    (Real.cosh (a*u) * Real.cosh (p*v)
      - Real.cosh (a*v) * Real.cosh (p*u))

/-- The factored odd carrier is exactly the generic symmetrized moment carrier
for `A=w*sinh(a·)`, `P=w*sinh(p·)`, `q=u^2`. -/
theorem oddWeightedSymmCarrier_eq_generic
    (w : ℝ → ℝ) (a p u v : ℝ) :
    oddWeightedSymmCarrier w a p u v =
      symmetrizedMomentIntegrand
        (fun x => w x * Real.sinh (a*x))
        (fun x => w x * Real.sinh (p*x))
        (fun x => x^2) (u,v) := by
  unfold oddWeightedSymmCarrier symmetrizedMomentIntegrand
  ring

/-- Even/cosh generic-carrier identification. -/
theorem evenWeightedSymmCarrier_eq_generic
    (w : ℝ → ℝ) (a p u v : ℝ) :
    evenWeightedSymmCarrier w a p u v =
      symmetrizedMomentIntegrand
        (fun x => w x * Real.cosh (a*x))
        (fun x => w x * Real.cosh (p*x))
        (fun x => x^2) (u,v) := by
  unfold evenWeightedSymmCarrier symmetrizedMomentIntegrand
  ring

private theorem sq_diff_pos_of_nonneg_lt
    {u v : ℝ} (hu : 0 <= u) (huv : u < v) :
    0 < v^2 - u^2 := by
  nlinarith

private theorem sq_diff_neg_of_nonneg_lt
    {u v : ℝ} (hv : 0 <= v) (hvu : v < u) :
    v^2 - u^2 < 0 := by
  nlinarith

/-- Global nonnegativity of the odd carrier on the nonnegative support
quadrant. -/
theorem oddWeightedSymmCarrier_nonneg
    {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 <= u) (hv : 0 <= v)
    (hwu : 0 <= w u) (hwv : 0 <= w v) :
    0 <= oddWeightedSymmCarrier w a p u v := by
  rcases lt_trichotomy u v with huv | huv | hvu
  · have hq : 0 < v^2 - u^2 := sq_diff_pos_of_nonneg_lt hu huv
    have hminor :
        0 < Real.sinh (a*u) * Real.sinh (p*v)
          - Real.sinh (a*v) * Real.sinh (p*u) := by
      have h := sinhKernel_strictTP2 ha hap (lt_of_le_of_lt hu huv) huv
      nlinarith [h]
    unfold oddWeightedSymmCarrier
    exact mul_nonneg (mul_nonneg hq.le (mul_nonneg hwu hwv)) hminor.le
  · subst v
    simp [oddWeightedSymmCarrier]
  · have hq : v^2 - u^2 < 0 := sq_diff_neg_of_nonneg_lt hv hvu
    have hswap := sinhKernel_strictTP2 ha hap (lt_of_le_of_lt hv hvu) hvu
    have hminor :
        Real.sinh (a*u) * Real.sinh (p*v)
          - Real.sinh (a*v) * Real.sinh (p*u) < 0 := by
      nlinarith [hswap]
    have hcore : 0 < (v^2-u^2) *
        (Real.sinh (a*u) * Real.sinh (p*v)
          - Real.sinh (a*v) * Real.sinh (p*u)) :=
      mul_pos_of_neg_of_neg hq hminor
    unfold oddWeightedSymmCarrier
    have hw : 0 <= w u * w v := mul_nonneg hwu hwv
    nlinarith [mul_nonneg hw hcore.le]

/-- Strict odd carrier positivity on every strictly ordered positive pair with
positive taper weights. -/
theorem oddWeightedSymmCarrier_pos
    {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 < u) (huv : u < v)
    (hwu : 0 < w u) (hwv : 0 < w v) :
    0 < oddWeightedSymmCarrier w a p u v := by
  have hq : 0 < v^2 - u^2 := sq_diff_pos_of_nonneg_lt hu.le huv
  have hminor :
      0 < Real.sinh (a*u) * Real.sinh (p*v)
        - Real.sinh (a*v) * Real.sinh (p*u) := by
    have h := sinhKernel_strictTP2 ha hap hu huv
    nlinarith [h]
  unfold oddWeightedSymmCarrier
  positivity

/-- Global nonnegativity of the even/cosh carrier on the nonnegative support
quadrant. -/
theorem evenWeightedSymmCarrier_nonneg
    {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 <= u) (hv : 0 <= v)
    (hwu : 0 <= w u) (hwv : 0 <= w v) :
    0 <= evenWeightedSymmCarrier w a p u v := by
  rcases lt_trichotomy u v with huv | huv | hvu
  · have hq : 0 < v^2 - u^2 := sq_diff_pos_of_nonneg_lt hu huv
    have hminor :
        0 < Real.cosh (a*u) * Real.cosh (p*v)
          - Real.cosh (a*v) * Real.cosh (p*u) := by
      have h := coshKernel_strictTP2 ha hap (lt_of_le_of_lt hu huv) huv
      nlinarith [h]
    unfold evenWeightedSymmCarrier
    exact mul_nonneg (mul_nonneg hq.le (mul_nonneg hwu hwv)) hminor.le
  · subst v
    simp [evenWeightedSymmCarrier]
  · have hq : v^2 - u^2 < 0 := sq_diff_neg_of_nonneg_lt hv hvu
    have hswap := coshKernel_strictTP2 ha hap (lt_of_le_of_lt hv hvu) hvu
    have hminor :
        Real.cosh (a*u) * Real.cosh (p*v)
          - Real.cosh (a*v) * Real.cosh (p*u) < 0 := by
      nlinarith [hswap]
    have hcore : 0 < (v^2-u^2) *
        (Real.cosh (a*u) * Real.cosh (p*v)
          - Real.cosh (a*v) * Real.cosh (p*u)) :=
      mul_pos_of_neg_of_neg hq hminor
    unfold evenWeightedSymmCarrier
    have hw : 0 <= w u * w v := mul_nonneg hwu hwv
    nlinarith [mul_nonneg hw hcore.le]

/-- Strict even carrier positivity on every strictly ordered positive pair with
positive taper weights. -/
theorem evenWeightedSymmCarrier_pos
    {w : ℝ → ℝ} {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hu : 0 < u) (huv : u < v)
    (hwu : 0 < w u) (hwv : 0 < w v) :
    0 < evenWeightedSymmCarrier w a p u v := by
  have hq : 0 < v^2 - u^2 := sq_diff_pos_of_nonneg_lt hu.le huv
  have hminor :
      0 < Real.cosh (a*u) * Real.cosh (p*v)
        - Real.cosh (a*v) * Real.cosh (p*u) := by
    have h := coshKernel_strictTP2 ha hap hu huv
    nlinarith [h]
  unfold evenWeightedSymmCarrier
  positivity

end Synthesis
