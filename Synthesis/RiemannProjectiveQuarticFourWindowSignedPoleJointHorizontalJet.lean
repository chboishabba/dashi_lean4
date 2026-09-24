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


/-!
## Exact q-variation and the favorable core inside the mixed cone

For fixed horizontal height alpha, the joint pair kernel is a cosine transform
of the same combined profile weighted by cosh(alpha*x).  Its variation in q is
therefore controlled by one first absolute moment.
-/

def QuarticFourSignedPolePair.signedPairQFirstMoment
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha : ℝ) : ℝ :=
  ∫ x : ℝ,
    |quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t x
      * Real.cosh (alpha*x)| * |x|

theorem QuarticFourSignedPolePair.signedPairQFirstMoment_nonneg
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.signedPairQFirstMoment alpha := by
  unfold QuarticFourSignedPolePair.signedPairQFirstMoment
  positivity

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedPairKernel alpha q
      =
    ∫ x : ℝ,
      quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x
        * Real.cosh (alpha*x)
        * Real.cos (q*x) := by
  unfold QuarticFourSignedPolePair.signedNormalizedPairKernel
    genericProjectivePairKernel
    quarticFourSignedPoleCombinedProfile
    profileLinearCombination
    quarticFourNormalizedProjectiveProfile
  have h1 :
      Integrable
        (fun x : ℝ =>
          genericProjectivePhysicalProfile
              (quarticFourWindowProfile W.R (1/2) W.muHalf) 1 x
            * Real.cosh (alpha*x)
            * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((quarticFourNormalizedProjectiveProfile_compact
        (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos).mul_right).mul_right)
  have h2 :
      Integrable
        (fun x : ℝ =>
          genericProjectivePhysicalProfile
              (quarticFourWindowProfile W.R (2/3) W.muTwo) 1 x
            * Real.cosh (alpha*x)
            * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((quarticFourNormalizedProjectiveProfile_compact
        (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos).mul_right).mul_right)
  rw [show
      (fun x : ℝ =>
        (quarticFourSmoothFinitePoleResidual W.R (2/3) W.muTwo t
            * genericProjectivePhysicalProfile
                (quarticFourWindowProfile W.R (1/2) W.muHalf) 1 x
          +
         (-quarticFourSmoothFinitePoleResidual W.R (1/2) W.muHalf t)
            * genericProjectivePhysicalProfile
                (quarticFourWindowProfile W.R (2/3) W.muTwo) 1 x)
          * Real.cosh (alpha*x) * Real.cos (q*x))
      =
      fun x =>
        quarticFourSmoothFinitePoleResidual W.R (2/3) W.muTwo t
          * (genericProjectivePhysicalProfile
              (quarticFourWindowProfile W.R (1/2) W.muHalf) 1 x
              * Real.cosh (alpha*x) * Real.cos (q*x))
        +
        (-quarticFourSmoothFinitePoleResidual W.R (1/2) W.muHalf t)
          * (genericProjectivePhysicalProfile
              (quarticFourWindowProfile W.R (2/3) W.muTwo) 1 x
              * Real.cosh (alpha*x) * Real.cos (q*x)) by
      funext x
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  ring

theorem QuarticFourSignedPolePair.signedPairQFirstMoment_integrable
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Integrable
      (fun x : ℝ =>
        |quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t x
          * Real.cosh (alpha*x)| * |x|) := by
  exact
    (((quarticFourSignedPoleCombinedProfile_continuous W.Rpos).mul
      (by fun_prop)).abs.mul continuous_abs)
      .integrable_of_hasCompactSupport
        (((quarticFourSignedPoleCombinedProfile_compact W.Rpos).mul_right).abs.mul_right)

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_lipschitz_q
    {t alpha p q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    |W.signedNormalizedPairKernel alpha q
      - W.signedNormalizedPairKernel alpha p|
      <=
    W.signedPairQFirstMoment alpha * |q-p| := by
  rw [W.signedNormalizedPairKernel_eq_combinedIntegral,
      W.signedNormalizedPairKernel_eq_combinedIntegral]
  have hiq :
      Integrable
        (fun x : ℝ =>
          quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t x
            * Real.cosh (alpha*x) * Real.cos (q*x)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((quarticFourSignedPoleCombinedProfile_compact W.Rpos).mul_right).mul_right)
  have hip :
      Integrable
        (fun x : ℝ =>
          quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t x
            * Real.cosh (alpha*x) * Real.cos (p*x)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((quarticFourSignedPoleCombinedProfile_compact W.Rpos).mul_right).mul_right)
  rw [← integral_sub hiq hip]
  have hdom :
      Integrable
        (fun x : ℝ =>
          |q-p| *
            (|quarticFourSignedPoleCombinedProfile
                W.R W.muHalf W.muTwo t x
              * Real.cosh (alpha*x)| * |x|)) :=
    (W.signedPairQFirstMoment_integrable).const_mul |q-p|
  calc
    |∫ x : ℝ,
      (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x
        * Real.cosh (alpha*x) * Real.cos (q*x)
      -
       quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x
        * Real.cosh (alpha*x) * Real.cos (p*x))|
      <=
    ∫ x : ℝ,
      |quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x
        * Real.cosh (alpha*x) * Real.cos (q*x)
      -
       quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t x
        * Real.cosh (alpha*x) * Real.cos (p*x)| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ x : ℝ,
      |q-p| *
        (|quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t x
          * Real.cosh (alpha*x)| * |x|) := by
      apply integral_mono (hiq.sub hip).abs hdom
      intro x
      have hc := Real.abs_cos_sub_cos_le (q*x) (p*x)
      have hfactor : |q*x-p*x| = |q-p| * |x| := by
        rw [← sub_mul, abs_mul]
      calc
        |quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t x
          * Real.cosh (alpha*x) * Real.cos (q*x)
        -
         quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t x
          * Real.cosh (alpha*x) * Real.cos (p*x)|
          =
        |quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t x
          * Real.cosh (alpha*x)|
          * |Real.cos (q*x)-Real.cos (p*x)| := by
            rw [← mul_sub, abs_mul]
        _ <=
        |quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t x
          * Real.cosh (alpha*x)| * |q*x-p*x| := by
          gcongr
        _ =
        |q-p| *
          (|quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t x
            * Real.cosh (alpha*x)| * |x|) := by
          rw [hfactor]
          ring
    _ =
      |q-p| * W.signedPairQFirstMoment alpha := by
        rw [integral_const_mul]
        rfl
    _ =
      W.signedPairQFirstMoment alpha * |q-p| := by ring

/--
Every off-line target-band height has a nonempty q-neighborhood on which the
exact pair kernel remains strictly negative.  The radius is chosen no larger
than |alpha|, hence this favorable core lies strictly inside q^2 < 6 alpha^2.
-/
theorem QuarticFourSignedPolePair.exists_negative_pairKernel_core
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha0 : 0 < |alpha|)
    (ha : |alpha| < W.eps) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 <= |alpha| ∧
      ∀ q : ℝ, |q| < q0 ->
        W.signedNormalizedPairKernel alpha q < 0 := by
  have hK0 :
      W.signedNormalizedPairKernel alpha 0 < 0 :=
    W.signedNormalizedPairKernel_zero_neg_of_targetBand ha0 ha
  let M := W.signedPairQFirstMoment alpha
  have hM : 0 <= M := W.signedPairQFirstMoment_nonneg
  by_cases hM0 : M = 0
  · refine ⟨|alpha|,ha0,le_rfl,?_⟩
    intro q hq
    have hvar :=
      W.signedNormalizedPairKernel_lipschitz_q
        (alpha:=alpha) (p:=0) (q:=q)
    rw [hM0, zero_mul] at hvar
    have heq :
        W.signedNormalizedPairKernel alpha q
          = W.signedNormalizedPairKernel alpha 0 := by
      rw [abs_nonpos_iff] at hvar
      exact sub_eq_zero.mp hvar
    rw [heq]
    exact hK0
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    let qstar := (-W.signedNormalizedPairKernel alpha 0) / (2*M)
    have hqstar : 0 < qstar := by
      dsimp [qstar]
      positivity
    let q0 := min |alpha| qstar
    have hq0 : 0 < q0 := lt_min ha0 hqstar
    refine ⟨q0,hq0,min_le_left _ _,?_⟩
    intro q hq
    have hqstar' : |q| < qstar :=
      lt_of_lt_of_le hq (min_le_right _ _)
    have hvar :=
      W.signedNormalizedPairKernel_lipschitz_q
        (alpha:=alpha) (p:=0) (q:=q)
    have hdiff :
        W.signedNormalizedPairKernel alpha q
          - W.signedNormalizedPairKernel alpha 0
          <= M * |q| := by
      exact le_trans (le_abs_self _) (by simpa [M] using hvar)
    have hsmall :
        M * |q|
          < -W.signedNormalizedPairKernel alpha 0 / 2 := by
      dsimp [qstar] at hqstar'
      rw [lt_div_iff₀ (show 0 < 2*M by positivity)] at hqstar'
      nlinarith
    linarith


/-!
## Complete homogeneous fourth-order joint jet

The earlier quartic polynomial extracted the mixed alpha^2*q^2 and pure q^4
terms, leaving the pure alpha^4 coefficient inside the horizontal remainder.
The same-ordinate identity identifies that missing coefficient exactly.

The complete fourth-order homogeneous form is

  S(W) * (alpha^2*q^2 - (alpha^4 + q^4)/6).
-/

def QuarticFourSignedPolePair.completeJointQuarticPolynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.targetStrength
    * (alpha^2 * q^2 - (alpha^4 + q^4)/6)

def QuarticFourSignedPolePair.completeJointQuarticRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha q : ℝ) : ℝ :=
  W.jointQuarticJetRemainder alpha q
    + (W.targetStrength/6) * alpha^4

theorem QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_completeQuarticJet
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedPairKernel alpha q
      =
    W.completeJointQuarticPolynomial alpha q
      + W.completeJointQuarticRemainder alpha q := by
  rw [W.signedNormalizedPairKernel_eq_quarticJet]
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
    QuarticFourSignedPolePair.completeJointQuarticRemainder
    QuarticFourSignedPolePair.jointQuarticJetPolynomial
  ring

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_zeroLine
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completeJointQuarticPolynomial alpha 0
      =
    -(W.targetStrength/6) * alpha^4 := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  ring

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_alphaZero
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completeJointQuarticPolynomial 0 q
      =
    -(W.targetStrength/6) * q^4 := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  ring

/--
Dimensionless sign polynomial in y=q^2/alpha^2:
  6 alpha^4 * signcore = -(y^2 - 6 y + 1).
This form avoids square roots and is suitable for exact cone refinements.
-/
theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_mul_six
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    6 * W.completeJointQuarticPolynomial alpha q
      =
    W.targetStrength
      * (6*alpha^2*q^2 - alpha^4 - q^4) := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  ring


/-!
## Rational sign regions of the complete fourth-order form

These avoid irrational root constants while already showing that the old
q^2 <= 6 alpha^2 cone is far too coarse.
-/

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_nonpos_inner
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hinner : 6 * q^2 <= alpha^2) :
    W.completeJointQuarticPolynomial alpha q <= 0 := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  have hS := W.targetStrength_pos.le
  have hq2 : 0 <= q^2 := sq_nonneg q
  have ha2 : 0 <= alpha^2 := sq_nonneg alpha
  have hcore :
      alpha^2 * q^2 - (alpha^4 + q^4)/6 <= 0 := by
    have ha4 : alpha^4 = alpha^2 * alpha^2 := by ring
    have hq4 : q^4 = q^2 * q^2 := by ring
    rw [ha4,hq4]
    nlinarith [mul_nonneg hq2 (sub_nonneg.mpr hinner)]
  exact mul_nonpos_of_nonneg_of_nonpos hS hcore

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_nonpos_outer
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (houter : 6 * alpha^2 <= q^2) :
    W.completeJointQuarticPolynomial alpha q <= 0 := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  have hS := W.targetStrength_pos.le
  have hq2 : 0 <= q^2 := sq_nonneg q
  have ha2 : 0 <= alpha^2 := sq_nonneg alpha
  have hcore :
      alpha^2 * q^2 - (alpha^4 + q^4)/6 <= 0 := by
    have ha4 : alpha^4 = alpha^2 * alpha^2 := by ring
    have hq4 : q^4 = q^2 * q^2 := by ring
    rw [ha4,hq4]
    nlinarith [mul_nonneg ha2 (sub_nonneg.mpr houter)]
  exact mul_nonpos_of_nonneg_of_nonpos hS hcore

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_pos_middle
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : alpha ≠ 0)
    (hlow : alpha^2 <= 2 * q^2)
    (hhigh : q^2 <= 2 * alpha^2) :
    0 < W.completeJointQuarticPolynomial alpha q := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  have hS := W.targetStrength_pos
  have ha2 : 0 < alpha^2 := sq_pos_of_ne_zero ha
  have hq2 : 0 < q^2 := by
    by_contra hq
    have hqz : q^2 = 0 := le_antisymm (le_of_not_gt hq) (sq_nonneg q)
    nlinarith
  have hcore :
      0 < alpha^2 * q^2 - (alpha^4 + q^4)/6 := by
    have ha4 : alpha^4 = alpha^2 * alpha^2 := by ring
    have hq4 : q^4 = q^2 * q^2 := by ring
    rw [ha4,hq4]
    nlinarith [
      mul_pos ha2 hq2,
      mul_nonneg ha2 (sub_nonneg.mpr hhigh),
      mul_nonneg hq2 (sub_nonneg.mpr hlow)]
  exact mul_pos hS hcore

/--
The old outer-good condition remains favorable for the complete quartic form,
but there is now also an inner favorable region near the same ordinate.
-/
theorem QuarticFourSignedPolePair.completeQuartic_has_two_favorable_regions
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (h : 6*q^2 <= alpha^2 ∨ 6*alpha^2 <= q^2) :
    W.completeJointQuarticPolynomial alpha q <= 0 := by
  rcases h with hinner | houter
  · exact W.completeJointQuarticPolynomial_nonpos_inner hinner
  · exact W.completeJointQuarticPolynomial_nonpos_outer houter


/-!
## Literal physical form of the complete quartic jet
-/

def QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * W.targetStrength
    * (heightOf sigma^2 * ((sigma : ℂ).im-t)^2
        - (heightOf sigma^4 + ((sigma : ℂ).im-t)^4)/6)
    / r^6

def QuarticFourSignedPolePair.literalCompleteJointQuarticRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let r := t/16
  let alpha := heightOf sigma / r
  let q := ((sigma : ℂ).im-t) / r
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
    * W.completeJointQuarticRemainder alpha q

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalCompleteJointQuarticPolynomial sigma
      =
    let r := t/16
    let alpha := heightOf sigma / r
    let q := ((sigma : ℂ).im-t) / r
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
      * W.completeJointQuarticPolynomial alpha q := by
  unfold QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial
    QuarticFourSignedPolePair.completeJointQuarticPolynomial
  dsimp
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_literalCompleteQuarticJet
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    W.literalCompleteJointQuarticPolynomial (sigma : Zeros)
      + W.literalCompleteJointQuarticRemainder (sigma : Zeros) := by
  rw [W.signedLiteralPairSourceTerm_eq_normalizedPairKernel ht]
  rw [W.signedNormalizedPairKernel_eq_completeQuarticJet]
  rw [W.literalCompleteJointQuarticPolynomial_eq_normalized ht]
  unfold QuarticFourSignedPolePair.literalCompleteJointQuarticRemainder
  dsimp
  ring

/--
Real fourth-harmonic coordinate underlying the complete quartic jet.
-/
def quarticSignedPoleFourthPhaseReal
    (alpha q : ℝ) : ℝ :=
  alpha^4 - 6*alpha^2*q^2 + q^4

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_eq_fourthPhase
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completeJointQuarticPolynomial alpha q
      =
    -(W.targetStrength/6)
      * quarticSignedPoleFourthPhaseReal alpha q := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
    quarticSignedPoleFourthPhaseReal
  ring

theorem quarticSignedPoleFourthPhaseReal_eq_complex_re
    (alpha q : ℝ) :
    quarticSignedPoleFourthPhaseReal alpha q
      =
    (((alpha : ℂ) + (q : ℂ) * Complex.I)^4).re := by
  unfold quarticSignedPoleFourthPhaseReal
  norm_num [pow_succ, Complex.mul_re, Complex.add_re]
  ring


/-!
## Fail-fast angular-sector obstruction to count-only arguments

The complete fourth-order form is positive on the diagonal q=alpha.  Thus
strip bounds and local multiplicity upper bounds alone cannot force the local
fourth-harmonic contribution to be favorable: an arbitrarily small admissible
point can lie in an adverse angular sector.
-/

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_diag
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completeJointQuarticPolynomial alpha alpha
      =
    (2/3 : ℝ) * W.targetStrength * alpha^4 := by
  unfold QuarticFourSignedPolePair.completeJointQuarticPolynomial
  ring

theorem QuarticFourSignedPolePair.completeJointQuarticPolynomial_diag_pos
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : alpha ≠ 0) :
    0 < W.completeJointQuarticPolynomial alpha alpha := by
  rw [W.completeJointQuarticPolynomial_diag]
  have hS := W.targetStrength_pos
  have ha4 : 0 < alpha^4 := by positivity
  positivity

/--
There are arbitrarily small strip/window-compatible normalized displacements
with adverse positive fourth-order contribution.  This is a geometry theorem,
not an assertion that zeta actually realizes the chosen point.
-/
theorem QuarticFourSignedPolePair.exists_arbitrarily_small_adverse_fourth_phase
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heps : 0 < eps) :
    ∃ alpha q : ℝ,
      0 < |alpha|
        ∧ |alpha| < eps
        ∧ q = alpha
        ∧ 0 < W.completeJointQuarticPolynomial alpha q := by
  let alpha : ℝ := min (eps/2) (1/4)
  have haPos : 0 < alpha := by
    dsimp [alpha]
    exact lt_min (by linarith) (by norm_num)
  have haeps : alpha < eps := by
    have hle : alpha <= eps/2 := min_le_left _ _
    linarith
  refine ⟨alpha,alpha,?_,?_,rfl,?_⟩
  · simpa [abs_of_pos haPos] using haPos
  · simpa [abs_of_pos haPos] using haeps
  · exact W.completeJointQuarticPolynomial_diag_pos haPos.ne'

/--
The physical fourth-harmonic phase itself is negative on the diagonal
delta=a, hence the literal leading source (which carries -S/6 times this
phase) is positive.
-/
theorem quarticSignedPolePhysicalFourthPhaseReal_diag
    (a : ℝ) :
    a^4 - 6*a^2*a^2 + a^4 = -4*a^4 := by
  ring



/-!
## Critical-line direction is favorable for the complete literal quartic jet
-/

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial_of_height_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (ha : heightOf sigma = 0) :
    W.literalCompleteJointQuarticPolynomial sigma
      =
    - (((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * W.targetStrength
        * ((sigma : ℂ).im-t)^4)
      / (6 * (t/16)^6) := by
  unfold QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial
  rw [ha]
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial_nonpos_of_height_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (ha : heightOf sigma = 0) :
    W.literalCompleteJointQuarticPolynomial sigma <= 0 := by
  rw [W.literalCompleteJointQuarticPolynomial_of_height_zero ht sigma ha]
  have hm : 0 <= ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hS : 0 <= W.targetStrength := W.targetStrength_pos.le
  have hd : 0 <= ((sigma : ℂ).im-t)^4 := by positivity
  have hr : 0 < 6 * (t/16)^6 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (mul_nonneg hm hS) hd))
    hr.le

theorem QuarticFourSignedPolePair.literalCompleteJointQuarticPolynomial_neg_of_height_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (ha : heightOf sigma = 0)
    (hdelta : (sigma : ℂ).im ≠ t) :
    W.literalCompleteJointQuarticPolynomial sigma < 0 := by
  rw [W.literalCompleteJointQuarticPolynomial_of_height_zero ht sigma ha]
  have hm :
      0 < ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by
    exact_mod_cast zetaZeroConfig.one_le_mult (sigma : ℂ) sigma.2
  have hS := W.targetStrength_pos
  have hd : 0 < ((sigma : ℂ).im-t)^4 := by
    positivity
  have hr : 0 < 6 * (t/16)^6 := by positivity
  exact div_neg_of_neg_of_pos
    (neg_neg.mpr (mul_pos (mul_pos hm hS) hd))
    hr


end Synthesis
