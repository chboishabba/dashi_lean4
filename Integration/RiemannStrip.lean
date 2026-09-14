import Integration.Levels
import Integration.TernaryHub
import Integration.RiemannReflection
import Spine.TernaryPhase
import Spine.TwoRegime

/-!
# The critical-strip reflection, and its descent to the common kernel

The analytic lane of the corpus is organised around one symmetry: the
functional-equation reflection `s ↦ 1 - s` of the completed zeta function,
together with the conjugation law `s ↦ conj s`.  This module works with those
two maps *as maps of `ℂ`* — nothing about zeta, its zeros, or any continuation
is used or claimed — and establishes the three things the global map needs:

1. **The critical line is exactly a fixed locus.**  The composite of the two
   declared symmetries is `critReflect s = 1 - conj s`, an involution of `ℂ`
   whose fixed set is precisely `{s | s.re = 1/2}` (`critReflect_fixed_iff`).
   So "critical line" is not extra vocabulary: it is the fixed sector of the
   kernel's involution, in the same sense as `Spine.MeanSplit`'s fixed sector.
2. **The displacement is the transverse coordinate.**  `displacement s =
   s.re - 1/2` is negated by the involution, vanishes exactly on the critical
   line, and embeds the strip into the binary contrast module `Spine.RealC2`
   with the reflection becoming `RealC2.swap` (`stripC2_swap`,
   `stripC2_sub_centre_mem_transverse`).
3. **The polarity classifier is the corpus's trit.**  The sign of the
   displacement is a balanced-ternary digit of the ternary hub, and the
   reflection acts on it as the hub's polarity involution `Trit.inv`
   (`stripTrit_critReflect`).  This is a preservation theorem, not an
   equivalence: `stripTrit` is surjective and very far from injective, and the
   boundary rows record that.

It also closes, in the only direction that is available without any analysis,
the adapter obligation stated in
`DASHI.Analysis.RiemannReflectionOrbitDefectExact` ("an analytic adapter must
separately prove that its zero/reflection data descends to this shape"): the
discrete `CentredState` model *embeds in the real displacement line*,
compatibly with reflection, magnitude, squared defect and polarity
(`modelDisplacement_*`).  What is **not** proved anywhere here is that any
actual zero data lands in that model; that remains an obligation of the analytic
specialist lane and is listed as such.

Finally, `envelope_neg` records that the generic two-regime envelope of
`Spine.TwoRegime` is reflection-invariant, so the kernel's frequency estimate is
a function of the displacement magnitude alone.
-/

namespace Integration.RiemannStrip

open Complex ComplexConjugate
open Integration.Levels
open Integration.RiemannReflection (CentredState Side reflect orbitMagnitude squaredDefect sideTrit)
open AgdaMirror.DASHIAlgebra (Trit)

/-! ## 1. The two declared symmetries -/

/-- The functional-equation reflection `s ↦ 1 - s`. -/
def xiReflect (s : ℂ) : ℂ := 1 - s

/-- The conjugation law's map. -/
def conjReflect (s : ℂ) : ℂ := conj s

/-- The composite of the two: the involution whose fixed locus is the critical
line. -/
def critReflect (s : ℂ) : ℂ := 1 - conj s

@[simp] theorem xiReflect_involutive (s : ℂ) : xiReflect (xiReflect s) = s := by
  simp [xiReflect]

@[simp] theorem conjReflect_involutive (s : ℂ) : conjReflect (conjReflect s) = s := by
  simp [conjReflect]

@[simp] theorem critReflect_involutive (s : ℂ) : critReflect (critReflect s) = s := by
  simp [critReflect]

@[simp] theorem critReflect_re (s : ℂ) : (critReflect s).re = 1 - s.re := by
  simp [critReflect]

@[simp] theorem critReflect_im (s : ℂ) : (critReflect s).im = s.im := by
  simp [critReflect]

/-- **The critical line is a fixed locus.**  `s` is fixed by the composite of
the functional equation and conjugation exactly when `Re s = 1/2`. -/
theorem critReflect_fixed_iff (s : ℂ) : critReflect s = s ↔ s.re = 1 / 2 := by
  rw [Complex.ext_iff]
  simp [critReflect]
  constructor <;> intro h <;> linarith

/-- The functional-equation reflection alone has a single fixed point. -/
theorem xiReflect_fixed_iff (s : ℂ) : xiReflect s = s ↔ s = 1 / 2 := by
  constructor
  · intro h
    have h2 : (2 : ℂ) * s = 1 := by
      simp only [xiReflect] at h
      linear_combination -h
    linear_combination h2 / 2
  · rintro rfl
    simp [xiReflect]
    ring

/-! ## 2. The displacement, and the binary contrast module -/

/-- The signed distance of `s` from the critical line. -/
noncomputable def displacement (s : ℂ) : ℝ := s.re - 1 / 2

@[simp] theorem displacement_critReflect (s : ℂ) :
    displacement (critReflect s) = - displacement s := by
  simp [displacement]; ring

@[simp] theorem displacement_xiReflect (s : ℂ) :
    displacement (xiReflect s) = - displacement s := by
  simp [displacement, xiReflect]; ring

theorem displacement_eq_zero_iff (s : ℂ) : displacement s = 0 ↔ s.re = 1 / 2 := by
  simp [displacement, sub_eq_zero]

/-- The strip abscissa placed in the binary contrast module `ℝ[C₂]`, as the pair
`(Re s, 1 - Re s)`. -/
noncomputable def stripC2 (s : ℂ) : Spine.RealC2.V :=
  WithLp.toLp 2 ![s.re, 1 - s.re]


@[simp] theorem stripC2_zero (s : ℂ) : stripC2 s 0 = s.re := rfl
@[simp] theorem stripC2_one (s : ℂ) : stripC2 s 1 = 1 - s.re := rfl

/-- **Level iv (preservation).**  The critical reflection of the analytic lane
becomes the generator of `C₂` acting on `ℝ[C₂]`. -/
theorem stripC2_swap (s : ℂ) :
    Spine.RealC2.swap (stripC2 s) = stripC2 (critReflect s) := by
  ext i
  fin_cases i <;> simp [stripC2]

/-- The centre of the strip in the same coordinates. -/
noncomputable def stripCentre : Spine.RealC2.V := WithLp.toLp 2 ![1 / 2, 1 / 2]

/-- The displacement is exactly the transverse (mean-zero) part of the strip
coordinate, in the sense of `Spine.RealC2.transverse`. -/
theorem stripC2_sub_centre_mem_transverse (s : ℂ) :
    stripC2 s - stripCentre ∈ Spine.RealC2.transverse := by
  rw [Spine.RealC2.mem_transverse_iff]
  simp [stripC2, stripCentre]
  ring

/-- …and its first coordinate is the displacement. -/
theorem stripC2_sub_centre_zero (s : ℂ) :
    (stripC2 s - stripCentre) 0 = displacement s := by
  simp [stripC2, stripCentre, displacement]

/-- The strip coordinate is fixed by the `C₂` generator exactly on the critical
line — the same statement as `critReflect_fixed_iff`, now inside the kernel's
fixed ⊕ transverse decomposition. -/
theorem stripC2_fixed_iff (s : ℂ) :
    Spine.RealC2.swap (stripC2 s) = stripC2 s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have := congrFun (congrArg (fun v : Spine.RealC2.V => (v : Fin 2 → ℝ)) h) 0
    simp [stripC2] at this
    linarith
  · intro h
    ext i
    fin_cases i <;> simp [stripC2] <;> linarith

/-! ## 3. The polarity classifier is the ternary hub's digit -/

/-- The sign of a real number as a balanced-ternary digit of the hub. -/
noncomputable def signTrit (x : ℝ) : Trit :=
  if x < 0 then .neg else if x = 0 then .zer else .pos

theorem signTrit_neg (x : ℝ) : signTrit (-x) = Trit.inv (signTrit x) := by
  unfold signTrit
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_neg (by linarith), if_neg (by linarith), if_pos h]; rfl
  · subst h; simp [Trit.inv]
  · rw [if_pos (by linarith), if_neg (by linarith), if_neg (by linarith)]; rfl

theorem signTrit_eq_zer_iff (x : ℝ) : signTrit x = .zer ↔ x = 0 := by
  unfold signTrit
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos h]; constructor <;> intro hx <;> simp_all
  · subst h; simp
  · rw [if_neg (by linarith), if_neg (by linarith)]
    constructor
    · intro hx; simp at hx
    · intro hx; linarith

/-- The polarity classifier of the critical strip. -/
noncomputable def stripTrit (s : ℂ) : Trit := signTrit (displacement s)

/-- **Level iv (preservation).**  The analytic lane's reflection acts on the
polarity classifier as the ternary hub's polarity involution. -/
theorem stripTrit_critReflect (s : ℂ) :
    stripTrit (critReflect s) = Trit.inv (stripTrit s) := by
  simp [stripTrit, signTrit_neg]

/-- The same for the functional-equation reflection alone. -/
theorem stripTrit_xiReflect (s : ℂ) :
    stripTrit (xiReflect s) = Trit.inv (stripTrit s) := by
  simp [stripTrit, signTrit_neg]

/-- The neutral digit is exactly the critical line. -/
theorem stripTrit_eq_zer_iff (s : ℂ) : stripTrit s = .zer ↔ s.re = 1 / 2 := by
  rw [stripTrit, signTrit_eq_zer_iff, displacement_eq_zero_iff]

theorem stripTrit_surjective : Function.Surjective stripTrit := by
  intro t
  cases t with
  | neg => exact ⟨0, by norm_num [stripTrit, signTrit, displacement]⟩
  | zer => exact ⟨(1 / 2 : ℂ), by norm_num [stripTrit, signTrit, displacement]⟩
  | pos => exact ⟨1, by norm_num [stripTrit, signTrit, displacement]⟩

/-- **Boundary.**  The classifier is not injective, so the analytic carrier is
not the hub's carrier: only the *sign* of the displacement transports, never the
displacement itself. -/
theorem stripTrit_not_injective : ¬ Function.Injective stripTrit := by
  intro h
  have : ((1 : ℂ)) = (2 : ℂ) := by
    refine h ?_
    norm_num [stripTrit, signTrit, displacement]
  norm_num [Complex.ext_iff] at this

/-! ## 4. The symmetry group of the strip is Klein four, not ternary -/

/-- The group generated by the functional equation and conjugation, as a
parameter pair: `(applyReflection, applyConjugation)`. -/
abbrev StripSymmetry : Type := Bool × Bool

/-- Its action on `ℂ`. -/
def act (g : StripSymmetry) (s : ℂ) : ℂ :=
  let t := if g.2 then conj s else s
  if g.1 then 1 - t else t

@[simp] theorem act_ff (s : ℂ) : act (false, false) s = s := rfl
@[simp] theorem act_tf (s : ℂ) : act (true, false) s = xiReflect s := rfl
@[simp] theorem act_ft (s : ℂ) : act (false, true) s = conjReflect s := rfl
@[simp] theorem act_tt (s : ℂ) : act (true, true) s = critReflect s := rfl

/-- The action is a group action of `(ℤ/2)²` written multiplicatively as
componentwise `xor`. -/
theorem act_comp (g h : StripSymmetry) (s : ℂ) :
    act g (act h s) = act (xor g.1 h.1, xor g.2 h.2) s := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := h
  cases g1 <;> cases g2 <;> cases h1 <;> cases h2 <;> simp [act]

/-- Every element of the group is an involution: the group has exponent 2. -/
theorem act_involutive (g : StripSymmetry) (s : ℂ) : act g (act g s) = s := by
  rw [act_comp]
  simp [act]

/-- The action is faithful: distinct parameters act differently. -/
theorem act_faithful {g h : StripSymmetry} (hgh : ∀ s, act g s = act h s) : g = h := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := h
  have hI := hgh Complex.I
  simp only [act] at hI
  cases g1 <;> cases g2 <;> cases h1 <;> cases h2 <;>
    first
      | rfl
      | (exfalso; revert hI; simp [Complex.ext_iff]; norm_num)
      | (exfalso; revert hI; simp [Complex.ext_iff])

/-- **Boundary.**  The strip's symmetry group has four elements, so it is not
the corpus's ternary carrier; the trit enters the analytic lane only as the
*sign of the displacement* (`stripTrit`), never as the symmetry itself. -/
theorem stripSymmetry_not_equiv_trit : ¬ Nonempty (StripSymmetry ≃ Trit) := by
  rintro ⟨e⟩
  have e' : StripSymmetry ≃ ZMod 3 := e.trans Integration.TernaryHub.balTritEquiv
  have := Fintype.card_congr e'
  simp at this

/-! ## 5. The discrete reflection model descends to the displacement line -/

/-- The Agda `CentredReflectionState` model, realised on the real displacement
line: the critical centre is `0`, and `offLine side n` is the displacement
`±(n+1)`. -/
def modelDisplacement : CentredState → ℝ
  | .criticalCentre => 0
  | .offLine .left n => -((n : ℝ) + 1)
  | .offLine .right n => (n : ℝ) + 1

/-- **Level iv (preservation).**  The model's reflection is negation of the
displacement, i.e. exactly the action of `critReflect` in the displacement
coordinate. -/
theorem modelDisplacement_reflect (x : CentredState) :
    modelDisplacement (reflect x) = - modelDisplacement x := by
  cases x with
  | criticalCentre => simp [modelDisplacement, reflect]
  | offLine s n => cases s <;> simp [modelDisplacement, reflect]

/-- The model's magnitude is the absolute displacement. -/
theorem modelDisplacement_abs (x : CentredState) :
    |modelDisplacement x| = (orbitMagnitude x : ℝ) := by
  cases x with
  | criticalCentre => simp [modelDisplacement, orbitMagnitude]
  | offLine s n =>
      have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      cases s
      · rw [show modelDisplacement (.offLine .left n) = -((n : ℝ) + 1) from rfl,
          abs_neg, abs_of_nonneg (by linarith)]
        simp [orbitMagnitude]
      · rw [show modelDisplacement (.offLine .right n) = ((n : ℝ) + 1) from rfl,
          abs_of_nonneg (by linarith)]
        simp [orbitMagnitude]

/-- The model's squared defect is the squared displacement. -/
theorem modelDisplacement_sq (x : CentredState) :
    modelDisplacement x ^ 2 = (squaredDefect x : ℝ) := by
  have h := modelDisplacement_abs x
  have : |modelDisplacement x| ^ 2 = ((orbitMagnitude x : ℝ)) ^ 2 := by rw [h]
  rw [sq_abs] at this
  rw [this, squaredDefect]
  push_cast
  ring

/-- The model's side classifier is the sign of the displacement: the discrete
carrier and the real line agree on the hub digit. -/
theorem signTrit_modelDisplacement (x : CentredState) :
    signTrit (modelDisplacement x) = sideTrit x := by
  cases x with
  | criticalCentre => simp [modelDisplacement, signTrit, sideTrit]
  | offLine s n =>
      have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      cases s
      · show signTrit (-((n : ℝ) + 1)) = Trit.neg
        rw [signTrit, if_pos (by linarith)]
      · show signTrit (((n : ℝ) + 1)) = Trit.pos
        rw [signTrit, if_neg (by push_neg; linarith), if_neg (by intro h; linarith)]

/-- The model embeds: distinct discrete states have distinct displacements. -/
theorem modelDisplacement_injective : Function.Injective modelDisplacement := by
  intro a b hab
  have hsign : sideTrit a = sideTrit b := by
    rw [← signTrit_modelDisplacement, ← signTrit_modelDisplacement, hab]
  have hmag : (orbitMagnitude a : ℝ) = orbitMagnitude b := by
    rw [← modelDisplacement_abs, ← modelDisplacement_abs, hab]
  have hmag' : orbitMagnitude a = orbitMagnitude b := by exact_mod_cast hmag
  cases a with
  | criticalCentre =>
      cases b with
      | criticalCentre => rfl
      | offLine s n => simp [orbitMagnitude] at hmag'
  | offLine sa na =>
      cases b with
      | criticalCentre => simp [orbitMagnitude] at hmag'
      | offLine sb nb =>
          have hn : na = nb := by simpa [orbitMagnitude] using hmag'
          have hs : sa = sb := by
            cases sa <;> cases sb <;>
              first | rfl | (exfalso; revert hsign; simp [sideTrit])
          subst hn; subst hs; rfl

/-! ## 6. The kernel's frequency envelope sees only the magnitude -/

/-- The generic two-regime envelope of `Spine.TwoRegime` is even, hence a
function of the displacement magnitude alone: an estimate on one side of the
critical line is automatically an estimate on the reflected side. -/
theorem envelope_neg (K₀ K₁ x : ℝ) :
    Spine.TwoRegime.envelope K₀ K₁ (-x) = Spine.TwoRegime.envelope K₀ K₁ x := by
  simp [Spine.TwoRegime.envelope]

/-- Consequently the envelope, read in the displacement coordinate, is invariant
under the critical reflection. -/
theorem envelope_displacement_critReflect (K₀ K₁ : ℝ) (s : ℂ) :
    Spine.TwoRegime.envelope K₀ K₁ (displacement (critReflect s)) =
      Spine.TwoRegime.envelope K₀ K₁ (displacement s) := by
  rw [displacement_critReflect, envelope_neg]

end Integration.RiemannStrip
