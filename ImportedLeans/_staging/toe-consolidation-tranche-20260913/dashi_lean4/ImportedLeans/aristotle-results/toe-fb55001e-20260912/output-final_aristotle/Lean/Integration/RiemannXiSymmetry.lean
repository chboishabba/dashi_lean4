import Integration.RiemannStrip

/-!
# The rational symmetry plane of the completed zeta, and its evaluation in `ℂ`

`DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact` builds the symmetry
geometry of the completed zeta function on an **exact rational coordinate
plane**: a pair of rationals, three involutions (conjugation, the
functional-equation reflection `s ↦ 1 - s`, and reflection across `Re s = 1/2`),
their composition laws, and the characterisation of the critical line as the
fixed line of the third.  It then declares four *obligation surfaces* as records
(`XiZeroSymmetry`, `NontrivialXiZero`, `ZeroCountingData`,
`PrimeZeroExplicitFormula`, `WeilPositivityCriterion`, `HilbertPolyaCandidate`)
and a nine-element `RiemannProofStage` enumeration.

This module does three things:

1. **Mirrors the rational plane** and re-proves its stated lemmas, strengthening
   the two one-directional critical-line lemmas into the iff
   `criticalLine_iff_fixed`.
2. **Evaluates the plane in `ℂ`** (`qToC`): the evaluation is injective and
   intertwines all three rational maps with the corresponding maps of
   `Integration.RiemannStrip` on `ℂ`, and carries the rational critical line
   exactly onto `Re s = 1/2`.  So the source's rational model is a faithful
   sub-picture of the complex statements, and the two developments are one
   object rather than two.
3. **Classifies the obligation surfaces.**  `XiZeroSymmetry` and
   `HilbertPolyaCandidate` are records whose fields are abstract types; each is
   inhabited by a content-free witness, so the theorems the source derives from
   them (`zeroQuartet`, `hilbertPolyaCandidateZerosLieOnCriticalLine`) are
   theorems *about the interface*, not about zeta.  The proof-stage enumeration
   is exactly a nine-element set (`stageEquiv`), i.e. a label ladder.

Nothing here mentions the actual zeta function; `isXiZero` is an abstract
predicate field throughout.
-/

namespace Integration.RiemannXiSymmetry

open Integration.Levels
open Integration.RiemannStrip (xiReflect conjReflect critReflect displacement)
open Complex ComplexConjugate

/-! ## 1. The rational coordinate plane -/

/-- Mirror of `RiemannXiSymmetryExact.ComplexCoordinate`. -/
structure QCoord where
  /-- The abscissa `σ`. -/
  re : ℚ
  /-- The ordinate `τ`. -/
  im : ℚ
  deriving DecidableEq, Repr

/-- Mirror of `conjugateCoordinate`. -/
def conjugateCoordinate (p : QCoord) : QCoord := ⟨p.re, -p.im⟩

/-- Mirror of `functionalReflection` (`s ↦ 1 - s`). -/
def functionalReflection (p : QCoord) : QCoord := ⟨1 - p.re, -p.im⟩

/-- Mirror of `criticalReflection` (reflection across `Re s = 1/2`). -/
def criticalReflection (p : QCoord) : QCoord := ⟨1 - p.re, p.im⟩

@[simp] theorem conjugate_involutive (p : QCoord) :
    conjugateCoordinate (conjugateCoordinate p) = p := by
  simp [conjugateCoordinate]

@[simp] theorem functionalReflection_involutive (p : QCoord) :
    functionalReflection (functionalReflection p) = p := by
  simp [functionalReflection]

@[simp] theorem criticalReflection_involutive (p : QCoord) :
    criticalReflection (criticalReflection p) = p := by
  simp [criticalReflection]

/-- Mirror of `functionalThenConjugateIsCritical`. -/
theorem conjugate_functional (p : QCoord) :
    conjugateCoordinate (functionalReflection p) = criticalReflection p := by
  simp [conjugateCoordinate, functionalReflection, criticalReflection]

/-- Mirror of `conjugateThenFunctionalIsCritical`. -/
theorem functional_conjugate (p : QCoord) :
    functionalReflection (conjugateCoordinate p) = criticalReflection p := by
  simp [conjugateCoordinate, functionalReflection, criticalReflection]

/-- Mirror of `conjugationCommutesWithFunctionalReflection`. -/
theorem conjugate_comm_functional (p : QCoord) :
    conjugateCoordinate (functionalReflection p) =
      functionalReflection (conjugateCoordinate p) := by
  rw [conjugate_functional, functional_conjugate]

/-- Mirror of `CriticalLine`. -/
def CriticalLine (p : QCoord) : Prop := p.re = 1 / 2

/-- Mirror of `CriticalStrip`. -/
def CriticalStrip (p : QCoord) : Prop := 0 < p.re ∧ p.re < 1

/-- The two one-directional lemmas of the source
(`criticalLineFixedByReflection`, `reflectionFixedImpliesCriticalLine`), as one
characterisation. -/
theorem criticalLine_iff_fixed (p : QCoord) :
    CriticalLine p ↔ criticalReflection p = p := by
  constructor
  · intro h
    have : (1 : ℚ) - p.re = p.re := by rw [h]; norm_num
    simp [criticalReflection, this]
  · intro h
    have h1 : (1 : ℚ) - p.re = p.re := congrArg QCoord.re h
    have : p.re = 1 / 2 := by linarith
    exact this

/-! ## 2. Evaluation in `ℂ` -/

/-- The rational plane evaluated in `ℂ`. -/
noncomputable def qToC (p : QCoord) : ℂ := { re := (p.re : ℝ), im := (p.im : ℝ) }

@[simp] theorem qToC_re (p : QCoord) : (qToC p).re = (p.re : ℝ) := rfl
@[simp] theorem qToC_im (p : QCoord) : (qToC p).im = (p.im : ℝ) := rfl

/-- The evaluation is injective. -/
theorem qToC_injective : Function.Injective qToC := by
  intro p q h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  cases p; cases q; simp_all

/-- **Level iv.**  Rational conjugation evaluates to complex conjugation. -/
theorem qToC_conjugate (p : QCoord) :
    qToC (conjugateCoordinate p) = conjReflect (qToC p) := by
  simp [qToC, conjugateCoordinate, conjReflect, Complex.ext_iff]

/-- **Level iv.**  The rational functional-equation reflection evaluates to
`s ↦ 1 - s`. -/
theorem qToC_functional (p : QCoord) :
    qToC (functionalReflection p) = xiReflect (qToC p) := by
  simp [qToC, functionalReflection, xiReflect, Complex.ext_iff]

/-- **Level iv.**  The rational critical reflection evaluates to
`s ↦ 1 - conj s`. -/
theorem qToC_critical (p : QCoord) :
    qToC (criticalReflection p) = critReflect (qToC p) := by
  simp [qToC, criticalReflection, critReflect, Complex.ext_iff]

/-- The rational critical line is exactly the complex critical line, and exactly
the vanishing of the displacement of `Integration.RiemannStrip`. -/
theorem qToC_criticalLine_iff (p : QCoord) :
    CriticalLine p ↔ (qToC p).re = 1 / 2 := by
  constructor
  · intro h
    rw [qToC_re, h]
    norm_num
  · intro h
    rw [qToC_re] at h
    have : ((p.re : ℝ)) = ((1 / 2 : ℚ) : ℝ) := by rw [h]; norm_num
    exact_mod_cast this

theorem qToC_displacement_eq_zero_iff (p : QCoord) :
    CriticalLine p ↔ displacement (qToC p) = 0 := by
  rw [qToC_criticalLine_iff, Integration.RiemannStrip.displacement_eq_zero_iff]

/-! ## 3. The obligation surfaces are interfaces -/

/-- Mirror of `XiZeroSymmetry`: an abstract zero predicate closed under the two
symmetries. -/
structure XiZeroSymmetry : Type 1 where
  /-- The abstract "is a zero of ξ" predicate. -/
  isXiZero : QCoord → Type
  /-- Closure under the functional equation. -/
  functionalEquationPreservesZero : ∀ p, isXiZero p → isXiZero (functionalReflection p)
  /-- Closure under conjugation. -/
  conjugationPreservesZero : ∀ p, isXiZero p → isXiZero (conjugateCoordinate p)

/-- Mirror of `zeroQuartet`: a zero has three companions. -/
def zeroQuartet (S : XiZeroSymmetry) (p : QCoord) (h : S.isXiZero p) :
    S.isXiZero (conjugateCoordinate p) × S.isXiZero (functionalReflection p) ×
      S.isXiZero (criticalReflection p) :=
  ⟨S.conjugationPreservesZero p h, S.functionalEquationPreservesZero p h,
    conjugate_functional p ▸
      S.conjugationPreservesZero _ (S.functionalEquationPreservesZero p h)⟩

/-- **Socket.**  The symmetry record is inhabited by an interface in which
everything is a zero, and by one in which nothing is, so the quartet theorem is
a statement about the interface and not about any zero set. -/
theorem xiZeroSymmetry_is_socket :
    (∃ S : XiZeroSymmetry, ∀ p, Nonempty (S.isXiZero p)) ∧
    (∃ S : XiZeroSymmetry, ∀ p, ¬ Nonempty (S.isXiZero p)) := by
  refine ⟨⟨⟨fun _ => PUnit, fun _ _ => PUnit.unit, fun _ _ => PUnit.unit⟩, fun _ => ⟨PUnit.unit⟩⟩,
    ⟨⟨fun _ => Empty, fun _ h => h.elim, fun _ h => h.elim⟩, ?_⟩⟩
  rintro p ⟨h⟩
  exact h.elim

/-- Mirror of `NontrivialXiZero`. -/
structure NontrivialXiZero (S : XiZeroSymmetry) where
  /-- The zero's coordinate. -/
  zeroCoordinate : QCoord
  /-- The zero witness. -/
  zeroWitness : S.isXiZero zeroCoordinate
  /-- Its membership of the critical strip. -/
  criticalStripWitness : CriticalStrip zeroCoordinate

/-- **Socket.**  A `NontrivialXiZero` exists for the content-free symmetry, so
inhabiting the record is not evidence about zeros. -/
theorem nontrivialXiZero_unconstrained :
    ∃ S : XiZeroSymmetry, Nonempty (NontrivialXiZero S) :=
  ⟨⟨fun _ => PUnit, fun _ _ => PUnit.unit, fun _ _ => PUnit.unit⟩,
    ⟨⟨⟨1 / 2, 0⟩, PUnit.unit, by constructor <;> norm_num [CriticalStrip]⟩⟩⟩

/-- Mirror of `HilbertPolyaCandidate`. -/
structure HilbertPolyaCandidate : Type 1 where
  /-- The abstract eigenvector type. -/
  Eigenvector : Type
  /-- Its (rational) eigenvalue. -/
  eigenvalue : Eigenvector → ℚ
  /-- The abstract self-adjointness/real-spectrum field. -/
  selfAdjointRealSpectrum : Type
  /-- The zero associated with an eigenvector. -/
  associatedZero : Eigenvector → QCoord
  /-- The law pinning that zero to the critical line. -/
  zeroCoordinateLaw : ∀ e, associatedZero e = ⟨1 / 2, eigenvalue e⟩

/-- Mirror of `hilbertPolyaCandidateZerosLieOnCriticalLine`. -/
theorem hilbertPolya_zeros_on_criticalLine (C : HilbertPolyaCandidate)
    (e : C.Eigenvector) : CriticalLine (C.associatedZero e) := by
  rw [CriticalLine, C.zeroCoordinateLaw e]

/-- **Socket.**  The candidate record is inhabited with an arbitrary eigenvalue
function and a vacuous self-adjointness field, so the previous theorem says only
that the record's own law was assumed: it is not evidence for a Hilbert–Pólya
operator. -/
theorem hilbertPolya_is_socket (f : ℕ → ℚ) :
    ∃ C : HilbertPolyaCandidate, C.Eigenvector = ℕ ∧ HEq C.eigenvalue f :=
  ⟨⟨ℕ, f, PUnit, fun n => ⟨1 / 2, f n⟩, fun _ => rfl⟩, rfl, HEq.rfl⟩

/-! ## 4. The proof-stage ladder is an enumeration -/

/-- Mirror of `RiemannProofStage`. -/
inductive RiemannProofStage
  | zetaDirichletSeries
  | meromorphicContinuation
  | completedXiFunctionalEquation
  | nontrivialZeroSymmetry
  | explicitPrimeZeroFormula
  | zeroCountingAsymptotics
  | weilPositivity
  | hilbertPolyaOperator
  | allNontrivialZerosCritical
  deriving DecidableEq, Repr, Fintype

/-- The source proves that the last two stages are distinct constructors.  In
fact the type is exactly a nine-element set: the ladder is a label enumeration,
carrying no implication from one stage to the next. -/
def stageEquiv : RiemannProofStage ≃ Fin 9 where
  toFun
    | .zetaDirichletSeries => 0
    | .meromorphicContinuation => 1
    | .completedXiFunctionalEquation => 2
    | .nontrivialZeroSymmetry => 3
    | .explicitPrimeZeroFormula => 4
    | .zeroCountingAsymptotics => 5
    | .weilPositivity => 6
    | .hilbertPolyaOperator => 7
    | .allNontrivialZerosCritical => 8
  invFun i :=
    match i with
    | 0 => .zetaDirichletSeries
    | 1 => .meromorphicContinuation
    | 2 => .completedXiFunctionalEquation
    | 3 => .nontrivialZeroSymmetry
    | 4 => .explicitPrimeZeroFormula
    | 5 => .zeroCountingAsymptotics
    | 6 => .weilPositivity
    | 7 => .hilbertPolyaOperator
    | 8 => .allNontrivialZerosCritical
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem stage_card : Fintype.card RiemannProofStage = 9 := by decide

end Integration.RiemannXiSymmetry
