import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Synthesis.RiemannG21CosineFourthRemainder
import Synthesis.RiemannG21PositivePlateauMoment
import Synthesis.RiemannG21OddDeterminantMargin

/-!
# Literal G21 finite even parity minor exists

This is the even/cosh analogue of the completed odd finite-minor compiler.
The literal positive-half moments are

  M0(y) = ∫ phi(u) cosh(yu) du,
  M2(y) = ∫ u^2 phi(u) cosh(yu) du,
  M4(y) = ∫ u^4 phi(u) cosh(yu) du.

The quadratic response truncation is

  Q_y(r) = M0(y) - r^2 M2(y)/2,

and at radii r,2r its determinant is exactly

  D_quad = -(3/2) r^2 Delta_even,

where `Delta_even = M0(a)M2(p)-M2(a)M0(p)`.

The cosine remainder obeys `|E_y(r)| <= |r|^4 M4(y)/24`.  After compact-support
bounds M2<=R^2 M0 and M4<=R^4 M0, the six-term determinant error normalizes to

  C_even <= M0(a)M0(p)/36 * (51 R^4 + 30 R^6 + 2 R^8).

Consequently the mass-free radius gate

  (51 R^4 + 30 R^6 + 2 R^8) r^2 < 54 (q_p-q_a)

preserves the strict finite determinant sign.  A positive taper plateau supplies
`Delta_even>0`, so such a finite `0<r<=1` exists.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

/-- Positive-half even/cosh response weight. -/
def evenHeightWeight (R : ℝ) (w : ℝ → ℝ) (y x : ℝ) : ℝ :=
  g21ClippedWeight R w x * Real.cosh (y*x)

def evenM0 (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, evenHeightWeight R w y x ∂volume

def evenM2 (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, x^2 * evenHeightWeight R w y x ∂volume

def evenM4 (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, x^4 * evenHeightWeight R w y x ∂volume

def evenRatio (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  evenM2 R w y / evenM0 R w y

/-- Support-only even determinant polynomial predicted by the radius-degree
normalization. -/
def g21EvenSupportPolynomial (R : ℝ) : ℝ :=
  51*R^4 + 30*R^6 + 2*R^8

theorem g21EvenSupportPolynomial_nonneg (R : ℝ) :
    0 <= g21EvenSupportPolynomial R := by
  unfold g21EvenSupportPolynomial
  positivity

private theorem evenHeightWeight_nonneg_all
    {w : ℝ → ℝ} {R y x : ℝ}
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= evenHeightWeight R w y x := by
  by_cases hx : x ∈ Icc (0:ℝ) R
  · unfold evenHeightWeight
    have hwc : 0 <= g21ClippedWeight R w x := by
      simpa [g21ClippedWeight, hx] using hw x hx
    exact mul_nonneg hwc (Real.cosh_pos _).le
  · simp [evenHeightWeight, g21ClippedWeight, hx]

/-- M0 is strictly positive from any positive taper plateau. -/
theorem evenM0_pos_of_positivePlateau
    {w : ℝ → ℝ} {y R l r : ℝ}
    (hl : 0 < l) (hlr : l < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (h0 : Integrable (evenHeightWeight R w y) volume) :
    0 < evenM0 R w y := by
  unfold evenM0
  apply integral_pos_of_nonneg_of_pos_on_posMeasure h0
  · intro x
    exact evenHeightWeight_nonneg_all hwNonneg
  · simp [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos, hlr]
  · intro x hx
    have hx0 : 0 < x := hl.trans hx.1
    have hxR : x < R := hx.2.trans hrR
    have hxI : x ∈ Icc (0:ℝ) R := ⟨hx0.le, hxR.le⟩
    unfold evenHeightWeight
    simp only [g21ClippedWeight, if_pos hxI]
    exact mul_pos (hwPos x hx) (Real.cosh_pos _)

private theorem evenM2_nonneg
    {w : ℝ → ℝ} {R y : ℝ}
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= evenM2 R w y := by
  unfold evenM2
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact mul_nonneg (sq_nonneg x) (evenHeightWeight_nonneg_all hw)

private theorem evenM4_nonneg
    {w : ℝ → ℝ} {R y : ℝ}
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= evenM4 R w y := by
  unfold evenM4
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact mul_nonneg (by positivity) (evenHeightWeight_nonneg_all hw)

/-- Direct compact-support M2/M4 domination on the full-line clipped carrier. -/
theorem literalEvenSupportMomentBounds
    {w : ℝ → ℝ} {R y : ℝ}
    (hR : 0 <= R)
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t)
    (h0 : Integrable (evenHeightWeight R w y) volume)
    (h2 : Integrable (fun x => x^2 * evenHeightWeight R w y x) volume)
    (h4 : Integrable (fun x => x^4 * evenHeightWeight R w y x) volume) :
    evenM2 R w y <= R^2 * evenM0 R w y ∧
    evenM4 R w y <= R^4 * evenM0 R w y := by
  have hpoint2 : ∀ x, x^2 * evenHeightWeight R w y x <=
      R^2 * evenHeightWeight R w y x := by
    intro x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hb : 0 <= evenHeightWeight R w y x := evenHeightWeight_nonneg_all hw
      have hs : x^2 <= R^2 := by nlinarith [hx.1, hx.2]
      exact mul_le_mul_of_nonneg_right hs hb
    · simp [evenHeightWeight, g21ClippedWeight, hx]
  have hpoint4 : ∀ x, x^4 * evenHeightWeight R w y x <=
      R^4 * evenHeightWeight R w y x := by
    intro x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · have hb : 0 <= evenHeightWeight R w y x := evenHeightWeight_nonneg_all hw
      have hs2 : x^2 <= R^2 := by nlinarith [hx.1, hx.2]
      have hs4 : x^4 <= R^4 := by nlinarith [sq_nonneg (x^2), sq_nonneg (R^2)]
      exact mul_le_mul_of_nonneg_right hs4 hb
    · simp [evenHeightWeight, g21ClippedWeight, hx]
  constructor
  · unfold evenM2 evenM0
    rw [← integral_const_mul]
    exact integral_mono h2 (h0.const_mul _) hpoint2
  · unfold evenM4 evenM0
    rw [← integral_const_mul]
    exact integral_mono h4 (h0.const_mul _) hpoint4

/-- Integrated fourth-order cosine remainder. -/
def evenCosRemainder
    (R : ℝ) (w : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ∫ x, evenHeightWeight R w y x *
    (Real.cos (r*x) - (1 - (r*x)^2/2)) ∂volume

/-- Literal integrated remainder bound `|E_y(r)|<=|r|^4 M4/24`. -/
theorem evenCosRemainder_le_M4
    {w : ℝ → ℝ} {R y r : ℝ}
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t)
    (h4 : Integrable (fun x => x^4 * evenHeightWeight R w y x) volume) :
    |evenCosRemainder R w y r| <= |r|^4 * evenM4 R w y / 24 := by
  let g : ℝ → ℝ := fun x => (|r|^4/24) * (x^4 * evenHeightWeight R w y x)
  have hg : Integrable g volume := by
    dsimp [g]
    exact h4.const_mul _
  have hpoint : ∀ x,
      ‖evenHeightWeight R w y x *
        (Real.cos (r*x) - (1 - (r*x)^2/2))‖ <= g x := by
    intro x
    have hb : 0 <= evenHeightWeight R w y x := evenHeightWeight_nonneg_all hw
    have hc := cos_quadratic_fourth_remainder (r*x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
    have habspow : |r*x|^4 = |r|^4 * |x|^4 := by rw [abs_mul, mul_pow]
    rw [habspow] at hc
    have hscaled := mul_le_mul_of_nonneg_left hc hb
    dsimp [g]
    have hx4 : |x|^4 = x^4 := by
      rw [abs_pow]
      norm_num
    rw [hx4] at hscaled
    nlinarith
  have hnorm := norm_integral_le_of_norm_le hg (Eventually.of_forall hpoint)
  unfold evenCosRemainder evenM4
  rw [Real.norm_eq_abs] at hnorm
  dsimp [g] at hnorm
  rw [integral_const_mul] at hnorm
  nlinarith

/-- Quadratic even response truncation. -/
def evenQuadraticTrunc (r m0 m2 : ℝ) : ℝ :=
  m0 - r^2*m2/2

def evenQuadraticDeterminant
    (r m0a m2a m0p m2p : ℝ) : ℝ :=
  evenQuadraticTrunc r m0a m2a * evenQuadraticTrunc (2*r) m0p m2p
    - evenQuadraticTrunc (2*r) m0a m2a * evenQuadraticTrunc r m0p m2p

def evenActualDeterminant
    (r m0a m2a m0p m2p ea1 ea2 ep1 ep2 : ℝ) : ℝ :=
  (evenQuadraticTrunc r m0a m2a + ea1) *
      (evenQuadraticTrunc (2*r) m0p m2p + ep2)
    - (evenQuadraticTrunc (2*r) m0a m2a + ea2) *
      (evenQuadraticTrunc r m0p m2p + ep1)

/-- Exact even quadratic determinant signal. -/
theorem evenQuadraticDeterminant_eq_signal
    {r m0a m2a m0p m2p : ℝ} :
    evenQuadraticDeterminant r m0a m2a m0p m2p =
      -((3:ℝ)/2)*r^2*(m0a*m2p-m2a*m0p) := by
  unfold evenQuadraticDeterminant evenQuadraticTrunc
  ring

/-- Same six-term algebra as the odd determinant. -/
theorem evenActualDeterminant_sub_quadratic
    {r m0a m2a m0p m2p ea1 ea2 ep1 ep2 : ℝ} :
    evenActualDeterminant r m0a m2a m0p m2p ea1 ea2 ep1 ep2
      - evenQuadraticDeterminant r m0a m2a m0p m2p
      = sixTermDetError
          (evenQuadraticTrunc r m0a m2a) (evenQuadraticTrunc (2*r) m0a m2a)
          (evenQuadraticTrunc r m0p m2p) (evenQuadraticTrunc (2*r) m0p m2p)
          ea1 ea2 ep1 ep2 := by
  unfold evenActualDeterminant evenQuadraticDeterminant sixTermDetError
  ring

private theorem evenTrunc_r_abs_le
    {r m0 m2 : ℝ} (hr0 : 0 <= r) (hr1 : r <= 1)
    (h0 : 0 <= m0) (h2 : 0 <= m2) :
    |evenQuadraticTrunc r m0 m2| <= m0 + m2/2 := by
  unfold evenQuadraticTrunc
  have hr2 : r^2 <= 1 := pow_le_one₀ hr0 hr1
  calc
    |m0-r^2*m2/2| <= |m0| + |r^2*m2/2| := abs_sub _ _
    _ = m0 + r^2*m2/2 := by
      rw [abs_of_nonneg h0, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 <= r^2),
        abs_of_nonneg h2]
      norm_num
    _ <= m0+m2/2 := by nlinarith

private theorem evenTrunc_2r_abs_le
    {r m0 m2 : ℝ} (hr0 : 0 <= r) (hr1 : r <= 1)
    (h0 : 0 <= m0) (h2 : 0 <= m2) :
    |evenQuadraticTrunc (2*r) m0 m2| <= m0 + 2*m2 := by
  unfold evenQuadraticTrunc
  have hr2 : r^2 <= 1 := pow_le_one₀ hr0 hr1
  calc
    |m0-(2*r)^2*m2/2| <= |m0| + |(2*r)^2*m2/2| := abs_sub _ _
    _ = m0 + 2*r^2*m2 := by
      rw [abs_of_nonneg h0, abs_div, abs_mul,
        abs_of_nonneg (by positivity : 0 <= (2*r)^2), abs_of_nonneg h2]
      norm_num
      ring
    _ <= m0+2*m2 := by nlinarith

/-- Even six-term coefficient. -/
def evenDeterminantErrorConstant
    (b1a b2a b1p b2p ca cp : ℝ) : ℝ :=
  16*b1a*cp + ca*b2p + b2a*cp + 16*ca*b1p + 32*ca*cp

private theorem six_abs_triangle_even (a b c d e f : ℝ) :
    |a+b+c-d-e-f| <= |a|+|b|+|c|+|d|+|e|+|f| := by
  calc
    |a+b+c-d-e-f| <= |a+b+c-d-e|+|f| := abs_sub _ _
    _ <= |a+b+c-d|+|e|+|f| := by nlinarith [abs_sub (a+b+c-d) e]
    _ <= |a+b+c|+|d|+|e|+|f| := by nlinarith [abs_sub (a+b+c) d]
    _ <= |a+b|+|c|+|d|+|e|+|f| := by nlinarith [abs_add (a+b) c]
    _ <= |a|+|b|+|c|+|d|+|e|+|f| := by nlinarith [abs_add a b]

private theorem evenSixTermError_le
    {r ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 b1a b2a b1p b2p ca cp : ℝ}
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (hb1a : 0 <= b1a) (hb2a : 0 <= b2a)
    (hb1p : 0 <= b1p) (hb2p : 0 <= b2p)
    (hca : 0 <= ca) (hcp : 0 <= cp)
    (hta1 : |ta1| <= b1a) (hta2 : |ta2| <= b2a)
    (htp1 : |tp1| <= b1p) (htp2 : |tp2| <= b2p)
    (hea1 : |ea1| <= r^4*ca) (hea2 : |ea2| <= 16*r^4*ca)
    (hep1 : |ep1| <= r^4*cp) (hep2 : |ep2| <= 16*r^4*cp) :
    |sixTermDetError ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2| <=
      r^4 * evenDeterminantErrorConstant b1a b2a b1p b2p ca cp := by
  have hr4 : 0 <= r^4 := by positivity
  have hr8le4 : r^8 <= r^4 := by
    rw [show r^8=r^4*r^4 by ring]
    have h4 : r^4 <= 1 := pow_le_one₀ hr0 hr1
    nlinarith [mul_le_mul_of_nonneg_left h4 hr4]
  have h1 : |ta1*ep2| <= r^4*(16*b1a*cp) := by
    rw [abs_mul]
    have := mul_le_mul hta1 hep2 (abs_nonneg _) hb1a
    nlinarith
  have h2 : |ea1*tp2| <= r^4*(ca*b2p) := by
    rw [abs_mul]
    have := mul_le_mul hea1 htp2 (abs_nonneg _) (mul_nonneg hr4 hca)
    nlinarith
  have h3 : |ea1*ep2| <= r^4*(16*ca*cp) := by
    rw [abs_mul]
    have hm := mul_le_mul hea1 hep2 (abs_nonneg _) (mul_nonneg hr4 hca)
    have hc : 0 <= 16*ca*cp := by positivity
    have hp := mul_le_mul_of_nonneg_right hr8le4 hc
    nlinarith
  have h4 : |ta2*ep1| <= r^4*(b2a*cp) := by
    rw [abs_mul]
    have := mul_le_mul hta2 hep1 (abs_nonneg _) hb2a
    nlinarith
  have h5 : |ea2*tp1| <= r^4*(16*ca*b1p) := by
    rw [abs_mul]
    have := mul_le_mul hea2 htp1 (abs_nonneg _) (by positivity)
    nlinarith
  have h6 : |ea2*ep1| <= r^4*(16*ca*cp) := by
    rw [abs_mul]
    have hm := mul_le_mul hea2 hep1 (abs_nonneg _) (by positivity)
    have hc : 0 <= 16*ca*cp := by positivity
    have hp := mul_le_mul_of_nonneg_right hr8le4 hc
    nlinarith
  unfold evenDeterminantErrorConstant sixTermDetError
  have ht := six_abs_triangle_even
    (ta1*ep2) (ea1*tp2) (ea1*ep2) (ta2*ep1) (ea2*tp1) (ea2*ep1)
  nlinarith

/-- Exact support-polynomial normalization of the even coefficient. -/
private theorem evenErrorConstant_le_supportPolynomial
    {R m0a m2a m4a m0p m2p m4p : ℝ}
    (hR : 0 <= R)
    (h0a : 0 <= m0a) (h2a0 : 0 <= m2a) (h4a0 : 0 <= m4a)
    (h0p : 0 <= m0p) (h2p0 : 0 <= m2p) (h4p0 : 0 <= m4p)
    (h2a : m2a <= R^2*m0a) (h4a : m4a <= R^4*m0a)
    (h2p : m2p <= R^2*m0p) (h4p : m4p <= R^4*m0p) :
    evenDeterminantErrorConstant
      (m0a+m2a/2) (m0a+2*m2a)
      (m0p+m2p/2) (m0p+2*m2p)
      (m4a/24) (m4p/24)
      <= (m0a*m0p/36) * g21EvenSupportPolynomial R := by
  have hb1a : m0a+m2a/2 <= m0a*(1+R^2/2) := by nlinarith
  have hb2a : m0a+2*m2a <= m0a*(1+2*R^2) := by nlinarith
  have hb1p : m0p+m2p/2 <= m0p*(1+R^2/2) := by nlinarith
  have hb2p : m0p+2*m2p <= m0p*(1+2*R^2) := by nlinarith
  have hca : m4a/24 <= m0a*R^4/24 := by nlinarith
  have hcp : m4p/24 <= m0p*R^4/24 := by nlinarith
  have ht1 : 16*(m0a+m2a/2)*(m4p/24) <=
      16*(m0a*(1+R^2/2))*(m0p*R^4/24) := by gcongr <;> positivity
  have ht2 : (m4a/24)*(m0p+2*m2p) <=
      (m0a*R^4/24)*(m0p*(1+2*R^2)) := by gcongr <;> positivity
  have ht3 : (m0a+2*m2a)*(m4p/24) <=
      (m0a*(1+2*R^2))*(m0p*R^4/24) := by gcongr <;> positivity
  have ht4 : 16*(m4a/24)*(m0p+m2p/2) <=
      16*(m0a*R^4/24)*(m0p*(1+R^2/2)) := by gcongr <;> positivity
  have ht5 : 32*(m4a/24)*(m4p/24) <=
      32*(m0a*R^4/24)*(m0p*R^4/24) := by gcongr <;> positivity
  unfold evenDeterminantErrorConstant g21EvenSupportPolynomial
  calc
    16*(m0a+m2a/2)*(m4p/24) + (m4a/24)*(m0p+2*m2p)
      + (m0a+2*m2a)*(m4p/24) + 16*(m4a/24)*(m0p+m2p/2)
      + 32*(m4a/24)*(m4p/24)
      <= 16*(m0a*(1+R^2/2))*(m0p*R^4/24)
        + (m0a*R^4/24)*(m0p*(1+2*R^2))
        + (m0a*(1+2*R^2))*(m0p*R^4/24)
        + 16*(m0a*R^4/24)*(m0p*(1+R^2/2))
        + 32*(m0a*R^4/24)*(m0p*R^4/24) := by linarith
    _ = (m0a*m0p/36)*(51*R^4+30*R^6+2*R^8) := by ring

/-- Any positive normalized even ratio gap admits a unit-scale radius satisfying
the support-only even gate. -/
theorem exists_unit_evenRadiusGate
    {R gap : ℝ} (hR : 0 <= R) (hgap : 0 < gap) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      g21EvenSupportPolynomial R*r^2 < 54*gap := by
  have ht : 0 < (54:ℝ)*gap := mul_pos (by norm_num) hgap
  obtain ⟨c,hc,hclt⟩ := exists_pos_mul_lt ht (g21EvenSupportPolynomial R)
  let r : ℝ := min c 1
  have hr : 0 < r := lt_min hc zero_lt_one
  have hr1 : r <= 1 := min_le_right _ _
  have hrc : r <= c := min_le_left _ _
  have hr2r : r^2 <= r := by nlinarith
  have hr2c : r^2 <= c := hr2r.trans hrc
  have hp : 0 <= g21EvenSupportPolynomial R := g21EvenSupportPolynomial_nonneg R
  have hm := mul_le_mul_of_nonneg_left hr2c hp
  exact ⟨r,hr,hr1,hm.trans_lt hclt⟩

/-- Division-free even Delta/ratio identity. -/
theorem evenDelta_eq_mass_mul_ratioGap
    {m0a m2a m0p m2p : ℝ}
    (h0a : 0 < m0a) (h0p : 0 < m0p) :
    m0a*m2p-m2a*m0p = m0a*m0p*(m2p/m0p-m2a/m0a) := by
  field_simp [h0a.ne',h0p.ne']
  ring

/-- Abstract finite even determinant closure from the even support gate. -/
theorem evenActualDeterminant_neg_of_supportGate
    {R r m0a m2a m4a m0p m2p m4p ea1 ea2 ep1 ep2 : ℝ}
    (hR : 0 <= R) (hr : 0 < r) (hr1 : r <= 1)
    (h0a : 0 < m0a) (h2a0 : 0 <= m2a) (h4a0 : 0 <= m4a)
    (h0p : 0 < m0p) (h2p0 : 0 <= m2p) (h4p0 : 0 <= m4p)
    (h2a : m2a <= R^2*m0a) (h4a : m4a <= R^4*m0a)
    (h2p : m2p <= R^2*m0p) (h4p : m4p <= R^4*m0p)
    (hgate : g21EvenSupportPolynomial R*r^2 < 54*(m2p/m0p-m2a/m0a))
    (hea1 : |ea1| <= r^4*(m4a/24)) (hea2 : |ea2| <= 16*r^4*(m4a/24))
    (hep1 : |ep1| <= r^4*(m4p/24)) (hep2 : |ep2| <= 16*r^4*(m4p/24)) :
    evenActualDeterminant r m0a m2a m0p m2p ea1 ea2 ep1 ep2 < 0 := by
  have hgap : 0 < m2p/m0p-m2a/m0a := by
    have hl : 0 <= g21EvenSupportPolynomial R*r^2 :=
      mul_nonneg (g21EvenSupportPolynomial_nonneg R) (sq_nonneg r)
    nlinarith
  have hdeltaId := evenDelta_eq_mass_mul_ratioGap h0a h0p
  have hdelta : 0 < m0a*m2p-m2a*m0p := by rw [hdeltaId]; positivity
  have hb1a0 : 0 <= m0a+m2a/2 := by positivity
  have hb2a0 : 0 <= m0a+2*m2a := by positivity
  have hb1p0 : 0 <= m0p+m2p/2 := by positivity
  have hb2p0 : 0 <= m0p+2*m2p := by positivity
  have hca0 : 0 <= m4a/24 := by positivity
  have hcp0 : 0 <= m4p/24 := by positivity
  have hta1 := evenTrunc_r_abs_le hr.le hr1 h0a.le h2a0
  have hta2 := evenTrunc_2r_abs_le hr.le hr1 h0a.le h2a0
  have htp1 := evenTrunc_r_abs_le hr.le hr1 h0p.le h2p0
  have htp2 := evenTrunc_2r_abs_le hr.le hr1 h0p.le h2p0
  have herr := evenSixTermError_le hr.le hr1
    hb1a0 hb2a0 hb1p0 hb2p0 hca0 hcp0
    hta1 hta2 htp1 htp2 hea1 hea2 hep1 hep2
  have hC := evenErrorConstant_le_supportPolynomial hR
    h0a.le h2a0 h4a0 h0p.le h2p0 h4p0 h2a h4a h2p h4p
  have herrSupport :
      |sixTermDetError
        (evenQuadraticTrunc r m0a m2a) (evenQuadraticTrunc (2*r) m0a m2a)
        (evenQuadraticTrunc r m0p m2p) (evenQuadraticTrunc (2*r) m0p m2p)
        ea1 ea2 ep1 ep2|
      <= r^4*((m0a*m0p/36)*g21EvenSupportPolynomial R) :=
    herr.trans (mul_le_mul_of_nonneg_left hC (by positivity))
  have hscale : 0 < r^2*(m0a*m0p/36) := by positivity
  have hgscaled := mul_lt_mul_of_pos_left hgate hscale
  have hstrict :
      r^4*((m0a*m0p/36)*g21EvenSupportPolynomial R)
        < ((3:ℝ)/2)*r^2*(m0a*m2p-m2a*m0p) := by
    rw [hdeltaId]
    nlinarith [hgscaled]
  have hdiff :
      |evenActualDeterminant r m0a m2a m0p m2p ea1 ea2 ep1 ep2
        - evenQuadraticDeterminant r m0a m2a m0p m2p|
      < |evenQuadraticDeterminant r m0a m2a m0p m2p| := by
    rw [evenActualDeterminant_sub_quadratic]
    have habs : |evenQuadraticDeterminant r m0a m2a m0p m2p|
        = ((3:ℝ)/2)*r^2*(m0a*m2p-m2a*m0p) := by
      rw [evenQuadraticDeterminant_eq_signal]
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3/2),
        abs_of_nonneg (sq_nonneg r), abs_of_pos hdelta]
    rw [habs]
    exact herrSupport.trans_lt hstrict
  have hcubic : evenQuadraticDeterminant r m0a m2a m0p m2p < 0 := by
    rw [evenQuadraticDeterminant_eq_signal]
    positivity
  exact negative_of_abs_sub_lt_abs hcubic hdiff

/-- Literal actual even determinant with integrated cosine remainders. -/
def literalEvenFiniteDeterminant
    (R : ℝ) (w : ℝ → ℝ) (a p r : ℝ) : ℝ :=
  evenActualDeterminant r
    (evenM0 R w a) (evenM2 R w a)
    (evenM0 R w p) (evenM2 R w p)
    (evenCosRemainder R w a r) (evenCosRemainder R w a (2*r))
    (evenCosRemainder R w p r) (evenCosRemainder R w p (2*r))

/-- End-to-end existence of a strict literal even parity minor. -/
theorem exists_literalEvenFiniteDeterminant_neg_of_positivePlateau
    {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (h0a : Integrable (evenHeightWeight R w a) volume)
    (h2a : Integrable (fun x => x^2 * evenHeightWeight R w a x) volume)
    (h4a : Integrable (fun x => x^4 * evenHeightWeight R w a x) volume)
    (h0p : Integrable (evenHeightWeight R w p) volume)
    (h2p : Integrable (fun x => x^2 * evenHeightWeight R w p x) volume)
    (h4p : Integrable (fun x => x^4 * evenHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧ literalEvenFiniteDeterminant R w a p r < 0 := by
  have hR : 0 <= R := (hl.trans (hlm.trans (hmr.trans hrR))).le
  have hM0a := evenM0_pos_of_positivePlateau hl (hlm.trans hmr) hrR hwNonneg hwPos h0a
  have hM0p := evenM0_pos_of_positivePlateau hl (hlm.trans hmr) hrR hwNonneg hwPos h0p
  have hM2a0 := evenM2_nonneg (y:=a) hwNonneg
  have hM2p0 := evenM2_nonneg (y:=p) hwNonneg
  have hM4a0 := evenM4_nonneg (y:=a) hwNonneg
  have hM4p0 := evenM4_nonneg (y:=p) hwNonneg
  have hcross : 0 < evenM0 R w a * evenM2 R w p - evenM2 R w a * evenM0 R w p := by
    simpa [evenM0, evenM2, evenHeightWeight, moment0, momentQ,
      mul_assoc, mul_left_comm, mul_comm] using
      (evenMomentCrossProduct_pos_of_positivePlateau
        ha hap hl hlm hmr hrR hwNonneg hwPos h0a h0p h2a h2p)
  have hratio : evenRatio R w a < evenRatio R w p := by
    unfold evenRatio
    apply oddRatioGap_of_crossProduct hM0a hM0p
    linarith
  obtain ⟨r,hr,hr1,hgate⟩ := exists_unit_evenRadiusGate hR (sub_pos.mpr hratio)
  have hsA := literalEvenSupportMomentBounds hR hwNonneg h0a h2a h4a
  have hsP := literalEvenSupportMomentBounds hR hwNonneg h0p h2p h4p
  have hea1raw := evenCosRemainder_le_M4 (r:=r) hwNonneg h4a
  have hea2raw := evenCosRemainder_le_M4 (r:=2*r) hwNonneg h4a
  have hep1raw := evenCosRemainder_le_M4 (r:=r) hwNonneg h4p
  have hep2raw := evenCosRemainder_le_M4 (r:=2*r) hwNonneg h4p
  have hea1 : |evenCosRemainder R w a r| <= r^4*(evenM4 R w a/24) := by
    simpa [abs_of_pos hr] using hea1raw
  have hep1 : |evenCosRemainder R w p r| <= r^4*(evenM4 R w p/24) := by
    simpa [abs_of_pos hr] using hep1raw
  have h2r : 0 < 2*r := by positivity
  have hea2 : |evenCosRemainder R w a (2*r)| <= 16*r^4*(evenM4 R w a/24) := by
    rw [abs_of_pos h2r] at hea2raw
    nlinarith
  have hep2 : |evenCosRemainder R w p (2*r)| <= 16*r^4*(evenM4 R w p/24) := by
    rw [abs_of_pos h2r] at hep2raw
    nlinarith
  have hneg := evenActualDeterminant_neg_of_supportGate hR hr hr1
    hM0a hM2a0 hM4a0 hM0p hM2p0 hM4p0
    hsA.1 hsA.2 hsP.1 hsP.2 hgate hea1 hea2 hep1 hep2
  exact ⟨r,hr,hr1,by unfold literalEvenFiniteDeterminant; exact hneg⟩

end Synthesis
