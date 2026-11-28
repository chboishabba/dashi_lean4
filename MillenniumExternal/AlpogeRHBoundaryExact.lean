import Problems.RiemannHypothesis.Millennium

/-!
# RH/Clay precise terminal handoff — source-independent and bidirectional

The external Alpöge Lean v4.33.1 submission defines
`_root_.riemannHypothesis : RiemannHypothesis` (module `Main`).
This local file deliberately **does not import the unlicensed submission**,
nor assume that a theorem name in another toolchain is a proof.

Once the source-pinned v4.33.1 module has been independently admitted and
a trusted *same-theorem* witness is made available in this environment, the
existing pinned Millennium target compiler closes the original Clay statement.
Both directions use the existing LeanDojo ↔ Mathlib weld, not another RH
proposition or a substitute zero carrier.

Source owner: the pinned Problems.RiemannHypothesis.Millennium. This narrow root adapter is re-elaborated verbatim by the isolated admission runner; unrelated Clay problem imports are not prerequisites.
-/

namespace MillenniumExternal.AlpogeRH

/-- Forward solve: a real Mathlib RH proof pays the existing exact Clay target. -/
theorem clay_of_admitted_mathlib
    (admitted : _root_.RiemannHypothesis) :
    Millennium.ClayRiemannHypothesis :=
  Millennium.ClayRiemannHypothesis.of_mathlib admitted

/-- Reverse solve: the exact Clay target returns to the *same* Mathlib RH. -/
theorem mathlib_of_clay
    (clay : Millennium.ClayRiemannHypothesis) :
    _root_.RiemannHypothesis :=
  Millennium.ClayRiemannHypothesis.mathlib clay

/-- Actual two-way statement identity; no missing analytic premise is smuggled in. -/
theorem clay_iff_mathlib :
    Millennium.ClayRiemannHypothesis ↔ _root_.RiemannHypothesis :=
  ⟨mathlib_of_clay, clay_of_admitted_mathlib⟩


/-- The actual pole-cancelled xi zero and nontrivial zeta zero
carriers, with the ORIGINAL inverse coordinate functions. No zero
count or critical-strip sampling is used. -/
noncomputable def originalXiZetaZeroEquiv :
    {t : ℂ // Millennium.xi t = 0} ≃
      {s : ℂ // Millennium.IsNontrivialZero s} where
  toFun t := ⟨Millennium.xi_argument t.1,
    Millennium.ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds.1
      t.1 t.2⟩
  invFun s := ⟨Millennium.zeta_zero_parameter s.1,
    Millennium.ClayRiemannHypothesis.Support.XiZetaZeroCorrespondence.holds.2
      s.1 s.2⟩
  left_inv t := Subtype.ext
    (Millennium.zeta_zero_parameter.comp_xi_argument t.1)
  right_inv s := Subtype.ext
    (Millennium.xi_argument.comp_zeta_zero_parameter s.1)

/-- Signed horizontal coordinate before any critical-line assumption.
The sign is not discarded by squaring or taking a norm. -/
theorem originalXiParameter_im (s : ℂ) :
    (Millennium.zeta_zero_parameter s).im = -(s.re - 1/2) := by
  simp [Millennium.zeta_zero_parameter, Complex.mul_im, Complex.sub_re]
  <;> ring


/-- The horizontal coordinate identity is reversible on the ORIGINAL
nontrivial-zeta/xi parameter, even before any external RH admission. -/
theorem originalXiParameter_im_zero_iff (s : ℂ) :
    (Millennium.zeta_zero_parameter s).im = 0 ↔
      s.re = (1/2 : ℝ) := by
  rw [originalXiParameter_im]
  constructor <;> intro h <;> linarith

/-- The actual xi-zero subtype carries precisely the same critical-line
predicate as its original zeta-zero image. This is a type-specific BIDI weld,
not a new proof that either condition holds for every zero. -/
theorem originalXiZeroOnAxis_iff_zetaCritical
    (t : {t : ℂ // Millennium.xi t = 0}) :
    t.1.im = 0 ↔
      (originalXiZetaZeroEquiv t).1.re = (1/2 : ℝ) := by
  change t.1.im = 0 ↔ (Millennium.xi_argument t.1).re = (1/2 : ℝ)
  have hc := originalXiParameter_im_zero_iff (Millennium.xi_argument t.1)
  rwa [Millennium.zeta_zero_parameter.comp_xi_argument] at hc


#print axioms originalXiZetaZeroEquiv
#print axioms originalXiParameter_im
#print axioms originalXiParameter_im_zero_iff
#print axioms originalXiZeroOnAxis_iff_zetaCritical
#print axioms clay_of_admitted_mathlib
#print axioms mathlib_of_clay
#print axioms clay_iff_mathlib

end MillenniumExternal.AlpogeRH
