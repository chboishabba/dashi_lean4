import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient

/-!
# Joint horizontal/ordinate jet for the signed four-window G3 source

The full centered-cubic discrepancy quotient is not an identity of the present
signed-pole witness lane.  The literal per-zero completed source nevertheless
contains a different fourth-order mechanism which must be kept coupled.

For the normalized projective pair kernel,

  H_G(alpha,q)
    = integral P_G(x) (cosh(alpha*x)-1) cos(q*x) dx,

split exactly

  cosh z - 1 = z^2/2 + (cosh z - 1 - z^2/2).

After the signed two-endpoint combination the quadratic horizontal coefficient
is

  Q_W(q) = integral P_comb(x) x^2 cos(q*x) dx
         = - compactCosineD2 P_comb q.

The paid moment geometry gives

  Q_W(0) = 0,
  Q_W'(0) = 0,
  Q_W''(0) = 4 * W.targetStrength > 0.

Thus the joint literal source has a genuine alpha^2 q^2 leading mechanism.
Under the physical normalization alpha=a/r and q=delta/r, together with the
outer r^-2 pair normalization, this has scale a^2 delta^2 / r^6.

No G3 inequality is claimed here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def genericProjectiveHorizontalQuadraticKernel
    (G : ℝ -> ℝ) (q : ℝ) : ℝ :=
  ∫ x : ℝ,
    genericProjectivePhysicalProfile G 1 x
      * x^2 * Real.cos (q*x)

def genericProjectiveHorizontalQuarticRemainder
    (G : ℝ -> ℝ) (alpha q : ℝ) : ℝ :=
  ∫ x : ℝ,
    genericProjectivePhysicalProfile G 1 x
      * (Real.cosh (alpha*x) - 1 - (alpha*x)^2/2)
      * Real.cos (q*x)

theorem genericProjectiveHorizontalKernel_eq_quadratic_add_remainder
    {G : ℝ -> ℝ}
    (hG : Continuous G)
    (hGc : HasCompactSupport G)
    (alpha q : ℝ) :
    genericProjectiveHorizontalKernel G alpha q
      =
    (alpha^2/2) * genericProjectiveHorizontalQuadraticKernel G q
      + genericProjectiveHorizontalQuarticRemainder G alpha q := by
  unfold genericProjectiveHorizontalKernel
    genericProjectiveHorizontalQuadraticKernel
    genericProjectiveHorizontalQuarticRemainder
  have hP : Continuous (genericProjectivePhysicalProfile G 1) :=
    genericProjectivePhysicalProfile_continuous hG 1
  have hPc : HasCompactSupport (genericProjectivePhysicalProfile G 1) :=
    genericProjectivePhysicalProfile_compact hGc 1
  have hq :
      Integrable
        (fun x : ℝ =>
          genericProjectivePhysicalProfile G 1 x
            * x^2 * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hPc.mul_right).mul_right)
  have hr :
      Integrable
        (fun x : ℝ =>
          genericProjectivePhysicalProfile G 1 x
            * (Real.cosh (alpha*x) - 1 - (alpha*x)^2/2)
            * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hPc.mul_right).mul_right)
  rw [← integral_const_mul, ← integral_add (hq.const_mul _) hr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    ring

theorem genericProjectiveHorizontalQuadraticKernel_eq_neg_compactCosineD2
    {G : ℝ -> ℝ}
    (q : ℝ) :
    genericProjectiveHorizontalQuadraticKernel G q
      =
    - compactCosineD2
        (genericProjectivePhysicalProfile G 1) q := by
  unfold genericProjectiveHorizontalQuadraticKernel compactCosineD2
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

def QuarticFourSignedPolePair.signedHorizontalQuadraticKernel
    {t : ℝ} (W : QuarticFourSignedPolePair t) (q : ℝ) : ℝ :=
  W.poleTwo *
      genericProjectiveHorizontalQuadraticKernel
        (quarticFourWindowProfile W.R (1/2) W.muHalf) q
    +
  (-W.poleHalf) *
      genericProjectiveHorizontalQuadraticKernel
        (quarticFourWindowProfile W.R (2/3) W.muTwo) q

def QuarticFourSignedPolePair.signedHorizontalQuarticRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.poleTwo *
      genericProjectiveHorizontalQuarticRemainder
        (quarticFourWindowProfile W.R (1/2) W.muHalf) alpha q
    +
  (-W.poleHalf) *
      genericProjectiveHorizontalQuarticRemainder
        (quarticFourWindowProfile W.R (2/3) W.muTwo) alpha q

def QuarticFourSignedPolePair.signedNormalizedHorizontalKernel
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.poleTwo *
      genericProjectiveHorizontalKernel
        (quarticFourWindowProfile W.R (1/2) W.muHalf) alpha q
    +
  (-W.poleHalf) *
      genericProjectiveHorizontalKernel
        (quarticFourWindowProfile W.R (2/3) W.muTwo) alpha q

theorem QuarticFourSignedPolePair.signedNormalizedHorizontalKernel_eq
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedHorizontalKernel alpha q
      =
    (alpha^2/2) * W.signedHorizontalQuadraticKernel q
      + W.signedHorizontalQuarticRemainder alpha q := by
  unfold QuarticFourSignedPolePair.signedNormalizedHorizontalKernel
    QuarticFourSignedPolePair.signedHorizontalQuadraticKernel
    QuarticFourSignedPolePair.signedHorizontalQuarticRemainder
  rw [genericProjectiveHorizontalKernel_eq_quadratic_add_remainder
        (quarticFourWindowProfile_continuous W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos),
      genericProjectiveHorizontalKernel_eq_quadratic_add_remainder
        (quarticFourWindowProfile_continuous W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos)]
  ring

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_eq_neg_D2
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedHorizontalQuadraticKernel q
      =
    - compactCosineD2
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q := by
  unfold QuarticFourSignedPolePair.signedHorizontalQuadraticKernel
  rw [genericProjectiveHorizontalQuadraticKernel_eq_neg_compactCosineD2,
      genericProjectiveHorizontalQuadraticKernel_eq_neg_compactCosineD2]
  unfold compactCosineD2
    quarticFourSignedPoleCombinedProfile profileLinearCombination
  have h1 :
      Integrable
        (fun x : ℝ =>
          - quarticFourNormalizedProjectiveProfile
              W.R (1/2) W.muHalf x
            * Real.cos (q*x) * x^2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (((quarticFourNormalizedProjectiveProfile_compact W.Rpos).neg.mul_right).mul_right)
  have h2 :
      Integrable
        (fun x : ℝ =>
          - quarticFourNormalizedProjectiveProfile
              W.R (2/3) W.muTwo x
            * Real.cos (q*x) * x^2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (((quarticFourNormalizedProjectiveProfile_compact W.Rpos).neg.mul_right).mul_right)
  rw [show
      (fun x : ℝ =>
        -(W.poleTwo *
            quarticFourNormalizedProjectiveProfile
              W.R (1/2) W.muHalf x
          + (-W.poleHalf) *
            quarticFourNormalizedProjectiveProfile
              W.R (2/3) W.muTwo x)
          * Real.cos (q*x) * x^2)
      =
      fun x =>
        W.poleTwo *
          (-quarticFourNormalizedProjectiveProfile
              W.R (1/2) W.muHalf x
            * Real.cos (q*x) * x^2)
        +
        (-W.poleHalf) *
          (-quarticFourNormalizedProjectiveProfile
              W.R (2/3) W.muTwo x
            * Real.cos (q*x) * x^2) by
      funext x
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  ring

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_zero
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedHorizontalQuadraticKernel 0 = 0 := by
  rw [W.signedHorizontalQuadraticKernel_eq_neg_D2]
  unfold compactCosineD2 profileSecondMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [show
      (∫ x : ℝ,
        -quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x * x^2)
        =
      - profileSecondMoment
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) by
        rw [integral_neg]
        rfl,
      quarticFourSignedPoleCombinedProfile_second_zero
        W.Rpos W.J2Half W.J2Two]
  ring

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_hasDerivAt
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    HasDerivAt W.signedHorizontalQuadraticKernel
      (- compactCosineD3
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q) q := by
  have hP :=
    quarticFourSignedPoleCombinedProfile_continuous
      (R:=W.R) (muHalf:=W.muHalf) (muTwo:=W.muTwo) W.Rpos
  have hPc :=
    quarticFourSignedPoleCombinedProfile_compact
      (R:=W.R) (muHalf:=W.muHalf) (muTwo:=W.muTwo) W.Rpos
  have h :=
    (compactCosineD2_deriv hP hPc q).neg
  convert h using 1
  funext x
  rw [W.signedHorizontalQuadraticKernel_eq_neg_D2]

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_deriv_zero
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    deriv W.signedHorizontalQuadraticKernel 0 = 0 := by
  rw [(W.signedHorizontalQuadraticKernel_hasDerivAt (q:=0)).deriv]
  unfold compactCosineD3
  simp

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_secondDeriv_zero
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    deriv (deriv W.signedHorizontalQuadraticKernel) 0
      = 4 * W.targetStrength := by
  have hP :=
    quarticFourSignedPoleCombinedProfile_continuous
      (R:=W.R) (muHalf:=W.muHalf) (muTwo:=W.muTwo) W.Rpos
  have hPc :=
    quarticFourSignedPoleCombinedProfile_compact
      (R:=W.R) (muHalf:=W.muHalf) (muTwo:=W.muTwo) W.Rpos
  have hfun :
      deriv W.signedHorizontalQuadraticKernel
        =
      fun q =>
        - compactCosineD3
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q := by
    funext q
    exact (W.signedHorizontalQuadraticKernel_hasDerivAt (q:=q)).deriv
  rw [hfun]
  have h :=
    (compactCosineD3_deriv hP hPc 0).neg
  rw [h.deriv]
  unfold compactCosineD4
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [show
      (∫ x : ℝ,
        quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x * x^4)
        =
      profileFourthMoment
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) by rfl,
      quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
  unfold QuarticFourSignedPolePair.targetStrength
  ring

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_secondDeriv_zero_pos
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 < deriv (deriv W.signedHorizontalQuadraticKernel) 0 := by
  rw [W.signedHorizontalQuadraticKernel_secondDeriv_zero]
  nlinarith [W.targetStrength_pos]


def QuarticFourSignedPolePair.signedNormalizedBaseKernel
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  W.poleTwo *
      genericProjectiveBaseKernel
        (quarticFourWindowProfile W.R (1/2) W.muHalf) 1 q
    +
  (-W.poleHalf) *
      genericProjectiveBaseKernel
        (quarticFourWindowProfile W.R (2/3) W.muTwo) 1 q

def QuarticFourSignedPolePair.signedNormalizedPairKernel
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.poleTwo *
      genericProjectivePairKernel
        (quarticFourWindowProfile W.R (1/2) W.muHalf) alpha q
    +
  (-W.poleHalf) *
      genericProjectivePairKernel
        (quarticFourWindowProfile W.R (2/3) W.muTwo) alpha q

theorem QuarticFourSignedPolePair.signedNormalizedBaseKernel_eq_compactCosine
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedBaseKernel q
      =
    compactCosineTransform
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) q := by
  unfold QuarticFourSignedPolePair.signedNormalizedBaseKernel
    genericProjectiveBaseKernel compactCosineTransform
    quarticFourSignedPoleCombinedProfile profileLinearCombination
  have h1 :
      Integrable
        (fun x : ℝ =>
          quarticFourNormalizedProjectiveProfile
            W.R (1/2) W.muHalf x * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (quarticFourNormalizedProjectiveProfile_compact W.Rpos).mul_right
  have h2 :
      Integrable
        (fun x : ℝ =>
          quarticFourNormalizedProjectiveProfile
            W.R (2/3) W.muTwo x * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (quarticFourNormalizedProjectiveProfile_compact W.Rpos).mul_right
  rw [show
      (fun x : ℝ =>
        (W.poleTwo *
            quarticFourNormalizedProjectiveProfile
              W.R (1/2) W.muHalf x
          + (-W.poleHalf) *
            quarticFourNormalizedProjectiveProfile
              W.R (2/3) W.muTwo x)
          * Real.cos (q*x))
      =
      fun x =>
        W.poleTwo *
          (quarticFourNormalizedProjectiveProfile
            W.R (1/2) W.muHalf x * Real.cos (q*x))
        +
        (-W.poleHalf) *
          (quarticFourNormalizedProjectiveProfile
            W.R (2/3) W.muTwo x * Real.cos (q*x)) by
      funext x
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  ring

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_base_add_horizontal
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedPairKernel alpha q
      =
    W.signedNormalizedBaseKernel q
      + W.signedNormalizedHorizontalKernel alpha q := by
  unfold QuarticFourSignedPolePair.signedNormalizedPairKernel
    QuarticFourSignedPolePair.signedNormalizedBaseKernel
    QuarticFourSignedPolePair.signedNormalizedHorizontalKernel
  rw [genericProjectivePairKernel_eq_base_add_horizontal
        (quarticFourWindowProfile_continuous W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos),
      genericProjectivePairKernel_eq_base_add_horizontal
        (quarticFourWindowProfile_continuous W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos)]
  ring

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_jointJet
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedPairKernel alpha q
      =
    compactCosineTransform
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q
      +
    (alpha^2/2) * W.signedHorizontalQuadraticKernel q
      +
    W.signedHorizontalQuarticRemainder alpha q := by
  rw [W.signedNormalizedPairKernel_eq_base_add_horizontal,
      W.signedNormalizedBaseKernel_eq_compactCosine,
      W.signedNormalizedHorizontalKernel_eq]
  ring

/--
Exact same-object transport of the literal off-ordinate G3 summand to the
normalized joint pair kernel.
-/
theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_normalizedPairKernel
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    ((zetaZeroConfig).mult ((sigma : Zeros) : ℂ) : ℝ) / (t/16)^2
      *
    W.signedNormalizedPairKernel
      (heightOf (sigma : Zeros) / (t/16))
      ((((sigma : Zeros) : ℂ).im - t) / (t/16)) := by
  unfold QuarticFourSignedPolePair.signedLiteralPairSourceTerm
    QuarticFourSignedPolePair.signedNormalizedPairKernel
    quarticFourPhysicalDetector
  rw [literalPairProjectiveDefect_rescale
        (quarticFourWindowProfile_contDiff
          (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos)
        (quarticFourWindowProfile_even W.R (1/2) W.muHalf)
        (by positivity : 0 < t/16) t (sigma : Zeros),
      literalPairProjectiveDefect_rescale
        (quarticFourWindowProfile_contDiff
          (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos)
        (quarticFourWindowProfile_even W.R (2/3) W.muTwo)
        (by positivity : 0 < t/16) t (sigma : Zeros)]
  ring

theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_jointJet
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    let r := t/16
    let alpha := heightOf (sigma : Zeros) / r
    let q := (((sigma : Zeros) : ℂ).im - t) / r
    ((zetaZeroConfig).mult ((sigma : Zeros) : ℂ) : ℝ) / r^2
      *
    (compactCosineTransform
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q
      + (alpha^2/2) * W.signedHorizontalQuadraticKernel q
      + W.signedHorizontalQuarticRemainder alpha q) := by
  rw [W.signedLiteralPairSourceTerm_eq_normalizedPairKernel ht]
  dsimp
  rw [W.signedNormalizedPairKernel_eq_jointJet]

end Synthesis
