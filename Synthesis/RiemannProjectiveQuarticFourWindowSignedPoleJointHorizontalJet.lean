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


/-!
## Quantitative local q² gain in the horizontal quadratic coefficient
-/

theorem exists_pos_right_of_second_deriv_pos
    {f f1 f2 : ℝ -> ℝ}
    (h01 : ∀ x : ℝ, HasDerivAt f (f1 x) x)
    (h12 : ∀ x : ℝ, HasDerivAt f1 (f2 x) x)
    (h2cont : Continuous f2)
    (hf0 : f 0 = 0)
    (hf10 : f1 0 = 0)
    (hf20 : 0 < f2 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ x : ℝ, 0 < x -> x < eps -> 0 < f x := by
  have hopen : IsOpen {x : ℝ | 0 < f2 x} :=
    isOpen_lt continuous_const h2cont
  have hmem : (0 : ℝ) ∈ {x : ℝ | 0 < f2 x} := hf20
  obtain ⟨eps,heps,hball⟩ :=
    (Metric.isOpen_iff.1 hopen) 0 hmem
  have hf2pos : ∀ x : ℝ, |x| < eps -> 0 < f2 x := by
    intro x hx
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
  have hf1cont : Continuous f1 :=
    continuous_of_forall_continuousAt fun x => (h12 x).continuousAt
  have hfcont : Continuous f :=
    continuous_of_forall_continuousAt fun x => (h01 x).continuousAt
  have hinc1 : StrictMonoOn f1 (Set.Icc (0 : ℝ) eps) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 eps)
      hf1cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h12 x).deriv]
    apply hf2pos x
    rw [abs_of_pos hx.1]
    exact hx.2
  have hf1pos :
      ∀ x : ℝ, 0 < x -> x < eps -> 0 < f1 x := by
    intro x hx0 hxe
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Set.Icc (0 : ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hinc1 h0 hx hx0
    rw [hf10] at h
    exact h
  have hinc : StrictMonoOn f (Set.Icc (0 : ℝ) eps) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 eps)
      hfcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h01 x).deriv]
    exact hf1pos x hx.1 hx.2
  refine ⟨eps,heps,?_⟩
  intro x hx0 hxe
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) eps := ⟨le_rfl,heps.le⟩
  have hx : x ∈ Set.Icc (0 : ℝ) eps := ⟨hx0.le,hxe.le⟩
  have h := hinc h0 hx hx0
  rw [hf0] at h
  exact h

theorem QuarticFourSignedPolePair.signedHorizontalQuadraticKernel_even
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    W.signedHorizontalQuadraticKernel (-q)
      = W.signedHorizontalQuadraticKernel q := by
  unfold QuarticFourSignedPolePair.signedHorizontalQuadraticKernel
    genericProjectiveHorizontalQuadraticKernel
  simp only [neg_mul, Real.cos_neg]

theorem QuarticFourSignedPolePair.exists_horizontalQuadraticKernel_gt_target_sq
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ,
        0 < |q| -> |q| < eps ->
        W.targetStrength * q^2
          < W.signedHorizontalQuadraticKernel q := by
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  let S := W.targetStrength
  let F : ℝ -> ℝ :=
    fun q => W.signedHorizontalQuadraticKernel q - S*q^2
  let F1 : ℝ -> ℝ :=
    fun q => -compactCosineD3 P q - 2*S*q
  let F2 : ℝ -> ℝ :=
    fun q => -compactCosineD4 P q - 2*S
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have h01 : ∀ q : ℝ, HasDerivAt F (F1 q) q := by
    intro q
    dsimp [F,F1,S,P]
    have hQ := W.signedHorizontalQuadraticKernel_hasDerivAt (q:=q)
    have hsq : HasDerivAt (fun x : ℝ => W.targetStrength*x^2)
        (2*W.targetStrength*q) q := by
      convert ((hasDerivAt_id q).pow 2).const_mul W.targetStrength using 1 <;> ring
    exact hQ.sub hsq
  have h12 : ∀ q : ℝ, HasDerivAt F1 (F2 q) q := by
    intro q
    dsimp [F1,F2,S,P]
    have hD :=
      (compactCosineD3_deriv hP hPc q).neg
    have hlin :
        HasDerivAt (fun x : ℝ => 2*W.targetStrength*x)
          (2*W.targetStrength) q := by
      convert (hasDerivAt_id q).const_mul (2*W.targetStrength) using 1 <;> ring
    exact hD.sub hlin
  have h2cont : Continuous F2 := by
    dsimp [F2,S,P]
    exact (compactCosineD4_continuous hP hPc).neg.sub continuous_const
  have hF0 : F 0 = 0 := by
    dsimp [F,S]
    rw [W.signedHorizontalQuadraticKernel_zero]
    ring
  have hF10 : F1 0 = 0 := by
    dsimp [F1,S,P]
    unfold compactCosineD3
    simp
  have hF20 : 0 < F2 0 := by
    dsimp [F2,S,P]
    have h4 :
        compactCosineD4
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) 0
          = -4 * W.targetStrength := by
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
    rw [h4]
    nlinarith [W.targetStrength_pos]
  obtain ⟨eps,heps,hpos⟩ :=
    exists_pos_right_of_second_deriv_pos
      h01 h12 h2cont hF0 hF10 hF20
  refine ⟨eps,heps,?_⟩
  intro q hq0 hqe
  by_cases hq : 0 <= q
  · have hqp : 0 < q := by
      rw [abs_of_nonneg hq] at hq0
      exact hq0
    have h := hpos q hqp (by simpa [abs_of_pos hqp] using hqe)
    dsimp [F,S] at h
    exact sub_pos.mp h
  · have hqn : q < 0 := lt_of_not_ge hq
    have hmq : 0 < -q := by linarith
    have hmabs : |-q| < eps := by simpa [abs_neg] using hqe
    have h := hpos (-q) hmq (by simpa [abs_of_pos hmq] using hmabs)
    dsimp [F,S] at h
    rw [W.signedHorizontalQuadraticKernel_even q] at h
    have hsq : (-q)^2 = q^2 := by ring
    rw [hsq] at h
    exact sub_pos.mp h

def QuarticFourSignedPolePair.literalHorizontalQuadraticTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  let alpha := heightOf sigma / r
  let q := ((sigma : ℂ).im-t) / r
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
    * ((alpha^2/2) * W.signedHorizontalQuadraticKernel q)

def QuarticFourSignedPolePair.literalHorizontalTargetScale
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * W.targetStrength
    * heightOf sigma ^ 2
    * ((sigma : ℂ).im-t)^2
    / (2 * (t/16)^6)

theorem QuarticFourSignedPolePair.literalHorizontalTargetScale_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalHorizontalTargetScale sigma
      =
    let r := t/16
    let alpha := heightOf sigma / r
    let q := ((sigma : ℂ).im-t) / r
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
      * ((alpha^2/2) * (W.targetStrength*q^2)) := by
  dsimp [QuarticFourSignedPolePair.literalHorizontalTargetScale]
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.literalHorizontalQuadraticTerm_ge_targetScale
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    {sigma : Zeros}
    {eps : ℝ}
    (hband :
      ∀ q : ℝ, 0 < |q| -> |q| < eps ->
        W.targetStrength*q^2
          < W.signedHorizontalQuadraticKernel q)
    (hq0 :
      0 < |((sigma : ℂ).im-t)/(t/16)|)
    (hqe :
      |((sigma : ℂ).im-t)/(t/16)| < eps) :
    W.literalHorizontalTargetScale sigma
      <= W.literalHorizontalQuadraticTerm sigma := by
  have hq :=
    hband (((sigma : ℂ).im-t)/(t/16)) hq0 hqe
  have hm :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hr : 0 < t/16 := by positivity
  have ha2 :
      0 <= (heightOf sigma / (t/16))^2 / 2 := by positivity
  have hfac :
      0 <=
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
        * ((heightOf sigma / (t/16))^2 / 2) := by positivity
  rw [W.literalHorizontalTargetScale_eq_normalized ht]
  unfold QuarticFourSignedPolePair.literalHorizontalQuadraticTerm
  dsimp
  exact mul_le_mul_of_nonneg_left hq.le hfac


/-!
## Literal joint gain/remainder normal form

The positive alpha^2 q^2 horizontal jet is useful only if the rest of the
literal pair source remains coupled.  These definitions keep the base cosine
term and the quartic horizontal remainder together as one joint remainder.
-/

def QuarticFourSignedPolePair.literalBaseTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  let q := ((sigma : ℂ).im-t) / r
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
    *
  compactCosineTransform
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) q

def QuarticFourSignedPolePair.literalHorizontalQuarticRemainderTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  let alpha := heightOf sigma / r
  let q := ((sigma : ℂ).im-t) / r
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
    *
  W.signedHorizontalQuarticRemainder alpha q

def QuarticFourSignedPolePair.literalJointNonquadraticRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  W.literalBaseTerm sigma
    + W.literalHorizontalQuarticRemainderTerm sigma

theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_literalJet
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    W.literalBaseTerm (sigma : Zeros)
      + W.literalHorizontalQuadraticTerm (sigma : Zeros)
      + W.literalHorizontalQuarticRemainderTerm (sigma : Zeros) := by
  rw [W.signedLiteralPairSourceTerm_eq_jointJet ht]
  unfold QuarticFourSignedPolePair.literalBaseTerm
    QuarticFourSignedPolePair.literalHorizontalQuadraticTerm
    QuarticFourSignedPolePair.literalHorizontalQuarticRemainderTerm
  dsimp
  ring

theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_quadratic_add_jointRemainder
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    W.literalHorizontalQuadraticTerm (sigma : Zeros)
      + W.literalJointNonquadraticRemainder (sigma : Zeros) := by
  rw [W.signedLiteralPairSourceTerm_eq_literalJet ht]
  unfold QuarticFourSignedPolePair.literalJointNonquadraticRemainder
  ring

/--
Local per-zero lower normal form on the horizontal q^2 gain band.

This deliberately does not assign a sign to the joint remainder.  It says
exactly that the paid horizontal quadratic term contributes at least the
explicit a^2 delta^2 / r^6 target scale, with every other effect retained in
one same-object remainder.
-/
theorem QuarticFourSignedPolePair.literalTargetScale_add_jointRemainder_le_pairSource
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    {sigma : ((SameOrd t)ᶜ : Set Zeros)}
    {eps : ℝ}
    (hband :
      ∀ q : ℝ, 0 < |q| -> |q| < eps ->
        W.targetStrength*q^2
          < W.signedHorizontalQuadraticKernel q)
    (hq0 :
      0 < |(((sigma : Zeros) : ℂ).im-t)/(t/16)|)
    (hqe :
      |(((sigma : Zeros) : ℂ).im-t)/(t/16)| < eps) :
    W.literalHorizontalTargetScale (sigma : Zeros)
      + W.literalJointNonquadraticRemainder (sigma : Zeros)
      <=
    W.signedLiteralPairSourceTerm sigma := by
  have hgain :=
    W.literalHorizontalQuadraticTerm_ge_targetScale
      ht W hband hq0 hqe
  rw [W.signedLiteralPairSourceTerm_eq_quadratic_add_jointRemainder ht]
  linarith

/--
Canonical local gain radius for the joint literal source.

This packages the existing horizontal quadratic jet theorem into the exact
per-zero normal form consumed by G3.
-/
theorem QuarticFourSignedPolePair.exists_literalTargetScale_add_jointRemainder_le_pairSource
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : ((SameOrd t)ᶜ : Set Zeros),
        0 < |(((sigma : Zeros) : ℂ).im-t)/(t/16)| ->
        |(((sigma : Zeros) : ℂ).im-t)/(t/16)| < eps ->
        W.literalHorizontalTargetScale (sigma : Zeros)
          + W.literalJointNonquadraticRemainder (sigma : Zeros)
          <=
        W.signedLiteralPairSourceTerm sigma := by
  obtain ⟨eps,heps,hband⟩ :=
    W.exists_horizontalQuadraticKernel_gt_target_sq
  refine ⟨eps,heps,?_⟩
  intro sigma hq0 hqe
  exact W.literalTargetScale_add_jointRemainder_le_pairSource
    ht W hband hq0 hqe


/-!
## Exact two-variable quartic joint jet

The base cosine channel and the horizontal quadratic channel have complementary
quartic geometry.  Rather than estimate them separately, extract their exact
joint polynomial and keep every higher-order term in one same-object remainder.
-/

def QuarticFourSignedPolePair.baseQuarticJetRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  compactCosineTransform
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) q
    + (W.targetStrength/6) * q^4

def QuarticFourSignedPolePair.horizontalQuadraticJetRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  W.signedHorizontalQuadraticKernel q
    - 2 * W.targetStrength * q^2

def QuarticFourSignedPolePair.jointQuarticJetRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.baseQuarticJetRemainder q
    + (alpha^2/2) * W.horizontalQuadraticJetRemainder q
    + W.signedHorizontalQuarticRemainder alpha q

def QuarticFourSignedPolePair.jointQuarticJetPolynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.targetStrength * (alpha^2 * q^2 - q^4/6)

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_quarticJet
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedPairKernel alpha q
      =
    W.jointQuarticJetPolynomial alpha q
      + W.jointQuarticJetRemainder alpha q := by
  rw [W.signedNormalizedPairKernel_eq_jointJet]
  unfold QuarticFourSignedPolePair.jointQuarticJetPolynomial
    QuarticFourSignedPolePair.jointQuarticJetRemainder
    QuarticFourSignedPolePair.baseQuarticJetRemainder
    QuarticFourSignedPolePair.horizontalQuadraticJetRemainder
  ring

/--
Physical quartic polynomial carried by one literal off-ordinate zero.

Writing
  a = beta - 1/2,
  delta = gamma - t,
  r = t/16,
this is exactly
  m_sigma * S(W) * (a^2 delta^2 - delta^4/6) / r^6.
-/
def QuarticFourSignedPolePair.literalJointQuarticPolynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * W.targetStrength
    * (heightOf sigma ^ 2 * ((sigma : ℂ).im-t)^2
        - ((sigma : ℂ).im-t)^4 / 6)
    / r^6

def QuarticFourSignedPolePair.literalJointQuarticRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  let alpha := heightOf sigma / r
  let q := ((sigma : ℂ).im-t) / r
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
    * W.jointQuarticJetRemainder alpha q

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalJointQuarticPolynomial sigma
      =
    let r := t/16
    let alpha := heightOf sigma / r
    let q := ((sigma : ℂ).im-t) / r
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
      * W.jointQuarticJetPolynomial alpha q := by
  unfold QuarticFourSignedPolePair.literalJointQuarticPolynomial
    QuarticFourSignedPolePair.jointQuarticJetPolynomial
  dsimp
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_literalQuarticJet
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    W.literalJointQuarticPolynomial (sigma : Zeros)
      + W.literalJointQuarticRemainder (sigma : Zeros) := by
  rw [W.signedLiteralPairSourceTerm_eq_normalizedPairKernel ht]
  rw [W.signedNormalizedPairKernel_eq_quarticJet]
  rw [W.literalJointQuarticPolynomial_eq_normalized ht]
  unfold QuarticFourSignedPolePair.literalJointQuarticRemainder
  dsimp
  ring

/--
The leading physical polynomial separates into the positive mixed
horizontal/ordinate gain and the negative pure-ordinate quartic term.
-/
theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_eq_mixed_sub_ordinate
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalJointQuarticPolynomial sigma
      =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * W.targetStrength
      * heightOf sigma^2
      * ((sigma : ℂ).im-t)^2
      / (t/16)^6
      -
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * W.targetStrength
      * ((sigma : ℂ).im-t)^4
      / (6 * (t/16)^6) := by
  unfold QuarticFourSignedPolePair.literalJointQuarticPolynomial
  field_simp [show t/16 ≠ 0 by positivity]
  ring


/-!
## Sign cone of the leading joint quartic polynomial
-/

theorem QuarticFourSignedPolePair.jointQuarticJetPolynomial_pos_of_sq_lt_six_sq
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : q ≠ 0)
    (hcone : q^2 < 6 * alpha^2) :
    0 < W.jointQuarticJetPolynomial alpha q := by
  unfold QuarticFourSignedPolePair.jointQuarticJetPolynomial
  have hS := W.targetStrength_pos
  have hq2 : 0 < q^2 := sq_pos_of_ne_zero hq
  have hbr :
      0 < alpha^2 * q^2 - q^4/6 := by
    have h6 : (0:ℝ) < 6 := by norm_num
    have hq4 : q^4 = q^2 * q^2 := by ring
    rw [hq4]
    have :
        q^2 / 6 < alpha^2 := by
      rw [div_lt_iff₀ h6]
      simpa [mul_comm] using hcone
    nlinarith
  exact mul_pos hS hbr

theorem QuarticFourSignedPolePair.jointQuarticJetPolynomial_neg_of_six_sq_lt_sq
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hcone : 6 * alpha^2 < q^2) :
    W.jointQuarticJetPolynomial alpha q < 0 := by
  unfold QuarticFourSignedPolePair.jointQuarticJetPolynomial
  have hS := W.targetStrength_pos
  have h6 : (0:ℝ) < 6 := by norm_num
  have hbr :
      alpha^2 * q^2 - q^4/6 < 0 := by
    have hq2 : 0 < q^2 := by
      have : 0 < 6 * alpha^2 + (q^2 - 6 * alpha^2) := by
        rw [add_sub_cancel]
        exact lt_of_le_of_lt (sq_nonneg _) hcone
      exact this
    have hq4 : q^4 = q^2 * q^2 := by ring
    rw [hq4]
    have :
        alpha^2 < q^2 / 6 := by
      rw [lt_div_iff₀ h6]
      simpa [mul_comm] using hcone
    nlinarith
  exact mul_neg_of_pos_of_neg hS hbr

theorem QuarticFourSignedPolePair.jointQuarticJetPolynomial_zero_of_sq_eq_six_sq
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hcone : q^2 = 6 * alpha^2) :
    W.jointQuarticJetPolynomial alpha q = 0 := by
  unfold QuarticFourSignedPolePair.jointQuarticJetPolynomial
  rw [hcone]
  ring

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_nonneg_of_delta_sq_le_six_height_sq
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (hcone :
      ((sigma : ℂ).im-t)^2 <= 6 * heightOf sigma^2) :
    0 <= W.literalJointQuarticPolynomial sigma := by
  unfold QuarticFourSignedPolePair.literalJointQuarticPolynomial
  have hm :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hS : 0 <= W.targetStrength := W.targetStrength_pos.le
  have hr : 0 < (t/16)^6 := by positivity
  have hbr :
      0 <=
        heightOf sigma^2 * ((sigma : ℂ).im-t)^2
          - ((sigma : ℂ).im-t)^4 / 6 := by
    have h6 : (0:ℝ) < 6 := by norm_num
    have hd2 : 0 <= ((sigma : ℂ).im-t)^2 := sq_nonneg _
    have hd4 :
        ((sigma : ℂ).im-t)^4
          = ((sigma : ℂ).im-t)^2 * ((sigma : ℂ).im-t)^2 := by ring
    rw [hd4]
    nlinarith
  exact div_nonneg (mul_nonneg (mul_nonneg hm hS) hbr) hr.le

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_nonpos_of_six_height_sq_le_delta_sq
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (hcone :
      6 * heightOf sigma^2 <= ((sigma : ℂ).im-t)^2) :
    W.literalJointQuarticPolynomial sigma <= 0 := by
  unfold QuarticFourSignedPolePair.literalJointQuarticPolynomial
  have hm :
      0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hS : 0 <= W.targetStrength := W.targetStrength_pos.le
  have hr : 0 < (t/16)^6 := by positivity
  have hbr :
      heightOf sigma^2 * ((sigma : ℂ).im-t)^2
        - ((sigma : ℂ).im-t)^4 / 6 <= 0 := by
    have hd2 : 0 <= ((sigma : ℂ).im-t)^2 := sq_nonneg _
    have hd4 :
        ((sigma : ℂ).im-t)^4
          = ((sigma : ℂ).im-t)^2 * ((sigma : ℂ).im-t)^2 := by ring
    rw [hd4]
    nlinarith
  have hnum :
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * W.targetStrength * hbr <= 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hm hS) hbr
  exact div_nonpos_of_nonpos_of_nonneg hnum hr.le


/-!
## Same-ordinate joint kernel equals minus four times the target defect

At q=0 the exact pair kernel is the hyperbolic/cosh channel used by the target
height detector.  This is an exact same-object identity, not a Taylor
approximation.
-/

theorem genericProjectivePairKernel_zero_eq_compactCosh
    (G : ℝ -> ℝ) (alpha : ℝ) :
    genericProjectivePairKernel G alpha 0
      =
    compactCoshTransform
      (genericProjectivePhysicalProfile G 1) alpha := by
  unfold genericProjectivePairKernel compactCoshTransform
  simp

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_zero_eq_neg_four_target
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedPairKernel alpha 0
      =
    -4 *
      quarticFourSignedPoleCombinedHeightDefect
        W.R W.muHalf W.muTwo t alpha := by
  unfold QuarticFourSignedPolePair.signedNormalizedPairKernel
  rw [genericProjectivePairKernel_zero_eq_compactCosh,
      genericProjectivePairKernel_zero_eq_compactCosh]
  rw [quarticFourSignedPoleCombinedHeightDefect_eq_cosh W.Rpos]
  unfold quarticFourSignedPoleCombinedProfile
    QuarticFourSignedPolePair.poleHalf
    QuarticFourSignedPolePair.poleTwo
  rw [compactCoshTransform_profileLinearCombination
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
      (quarticFourNormalizedProjectiveProfile_continuous
        (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)
      (quarticFourNormalizedProjectiveProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)]
  ring

/--
On the already-paid target band, the exact same-ordinate joint pair kernel is
strictly negative.  Thus the nominal mixed cone contains a favorable core; the
positive-part ConeDebt abstraction intentionally discards this negative mass.
-/
theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_zero_neg_of_targetBand
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha0 : 0 < |alpha|)
    (ha : |alpha| < W.eps) :
    W.signedNormalizedPairKernel alpha 0 < 0 := by
  rw [W.signedNormalizedPairKernel_zero_eq_neg_four_target]
  have hD :=
    W.combinedTargetBand alpha ha0 ha
  nlinarith

end Synthesis
