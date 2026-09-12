import Integration.Levels
import Integration.TernaryHub
import Spine.TernaryPhase

/-!
# The analytic lane's reflection carrier, and its genuine link to the ternary hub

This is the first of three modules that bring the RH/zeta *analytic* lane of the
corpus into the global integration map.  It is a faithful Lean mirror of two
Agda modules and nothing more:

* `DASHI.Analysis.RiemannReflectionOrbitDefectExact` — the discrete
  "centred displacement" carrier: a fixed critical centre plus left/right
  off-line states carrying a natural-number magnitude, with the reflection
  exchanging the two sides, the orientation-forgetting quotient, and the
  squared defect.
* `DASHI.Analysis.RiemannReflectionC3OrbitShapeBridgeExact` — the three-phase
  `C3Phase` carrier with its inversion, the phase values in the cyclotomic
  layer, and the `OrbitRole` comparison (fixed vs inverse-pair).

The Agda file states the comparison as an *orbit-shape* analogy and records
`c3AndZetaCarriersIdentified = false` as a `Bool` boundary flag.  Here that flag
is replaced by a theorem (`c3_not_equiv_centred`), and the parts of the analogy
that *are* genuine are upgraded to level-iv witnesses of
`Integration.Levels`:

* `centredPolarTransport` — the reflection carrier *is* the ternary hub's
  polarity carrier tensored with a magnitude, and the reflection *is* the hub's
  polarity involution;
* `sideTrit_reflect` — the side classifier is polarity-equivariant;
* `c3Transport` — `C3Phase` with its inversion is the hub's `Trit` with `inv`;
* `phaseC_invert`, `phaseC_sum` — the three phases realised as the actual cube
  roots of unity of `Spine.TernaryPhase`, with inversion becoming complex
  conjugation and the orbit sum genuinely vanishing in `ℂ` (the Agda proves the
  corresponding cancellation in its own finite cyclotomic model).

Nothing here is a statement about the Riemann zeta function, its zeros, or the
Riemann hypothesis: `CentredState` is a discrete carrier and `C3Phase` is a
three-element set.  Whether any analytic zero data descends to `CentredState` is
exactly the adapter obligation the Agda source flags, and it is *not* discharged
here; what `Integration.RiemannStrip` does supply is the descent of the
*complex-strip reflection* to the real displacement line and to the trit.
-/

namespace Integration.RiemannReflection

open Integration.Levels
open AgdaMirror.DASHIAlgebra (Trit)
open Complex ComplexConjugate

/-! ## 1. The mirrored carriers -/

/-- Mirror of `RiemannReflectionOrbitDefectExact.ReflectionSide`. -/
inductive Side | left | right
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `RiemannReflectionOrbitDefectExact.CentredReflectionState`: the
critical centre, or an off-line state with a side and a magnitude predecessor.
`offLine s n` denotes displacement magnitude `n + 1`, which is the source's own
convention (it prevents a duplicate off-line encoding at distance zero). -/
inductive CentredState
  | criticalCentre
  | offLine (side : Side) (pred : ℕ)
  deriving DecidableEq, Repr

/-- Mirror of `RiemannReflectionOrbitDefectExact.reflect`. -/
def reflect : CentredState → CentredState
  | .criticalCentre => .criticalCentre
  | .offLine .left n => .offLine .right n
  | .offLine .right n => .offLine .left n

@[simp] theorem reflect_centre : reflect .criticalCentre = .criticalCentre := rfl

/-- The reflection is an involution (Agda `reflectInvolutive`). -/
theorem reflect_involutive (x : CentredState) : reflect (reflect x) = x := by
  cases x with
  | criticalCentre => rfl
  | offLine s _ => cases s <;> rfl

/-- The critical centre is the *only* fixed point (Agda states the two
directions separately as `criticalCentreFixed` and
`reflectionFixedImpliesCriticalCentre`). -/
theorem reflect_fixed_iff (x : CentredState) :
    reflect x = x ↔ x = .criticalCentre := by
  constructor
  · intro h
    cases x with
    | criticalCentre => rfl
    | offLine s _ => cases s <;> simp [reflect] at h
  · rintro rfl; rfl

/-- Mirror of `orbitMagnitude`. -/
def orbitMagnitude : CentredState → ℕ
  | .criticalCentre => 0
  | .offLine _ n => n + 1

/-- Mirror of `squaredDefect`. -/
def squaredDefect (x : CentredState) : ℕ := orbitMagnitude x * orbitMagnitude x

/-- The magnitude is reflection-invariant (Agda
`orbitMagnitudeReflectionInvariant`). -/
@[simp] theorem orbitMagnitude_reflect (x : CentredState) :
    orbitMagnitude (reflect x) = orbitMagnitude x := by
  cases x with
  | criticalCentre => rfl
  | offLine s _ => cases s <;> rfl

/-- Hence so is the squared defect. -/
@[simp] theorem squaredDefect_reflect (x : CentredState) :
    squaredDefect (reflect x) = squaredDefect x := by
  simp [squaredDefect]

/-- Zero magnitude characterises the critical centre. -/
theorem orbitMagnitude_eq_zero_iff (x : CentredState) :
    orbitMagnitude x = 0 ↔ x = .criticalCentre := by
  cases x with
  | criticalCentre => simp [orbitMagnitude]
  | offLine s n => cases s <;> simp [orbitMagnitude]

/-! ## 2. The side classifier is the hub's polarity -/

/-- The side of a centred state, as a balanced-ternary digit of the corpus's
ternary hub: left is negative, right is positive, the critical centre is the
neutral digit. -/
def sideTrit : CentredState → Trit
  | .criticalCentre => .zer
  | .offLine .left _ => .neg
  | .offLine .right _ => .pos

/-- **Level iv (preservation).**  The reflection of the analytic lane becomes
the hub's polarity involution `Trit.inv` under the side classifier. -/
theorem sideTrit_reflect (x : CentredState) :
    sideTrit (reflect x) = Trit.inv (sideTrit x) := by
  cases x with
  | criticalCentre => rfl
  | offLine s _ => cases s <;> rfl

/-- The neutral digit is exactly the critical centre. -/
theorem sideTrit_eq_zer_iff (x : CentredState) :
    sideTrit x = .zer ↔ x = .criticalCentre := by
  cases x with
  | criticalCentre => simp [sideTrit]
  | offLine s n => cases s <;> simp [sideTrit]

theorem sideTrit_surjective : Function.Surjective sideTrit := by
  intro t
  cases t with
  | neg => exact ⟨.offLine .left 0, rfl⟩
  | zer => exact ⟨.criticalCentre, rfl⟩
  | pos => exact ⟨.offLine .right 0, rfl⟩

/-- …but not injective: the magnitude survives the classifier, which is why the
next result needs the magnitude as a second coordinate. -/
theorem sideTrit_not_injective : ¬ Function.Injective sideTrit := by
  intro h
  have : (CentredState.offLine .left 0) = CentredState.offLine .left 1 :=
    h (by rfl)
  simp at this

/-! ## 3. Polar coordinates: the carrier *is* polarity × magnitude -/

/-- Polar coordinates for the reflection carrier: a hub digit together with a
magnitude, subject to the source's own convention that the neutral digit occurs
exactly at magnitude zero. -/
def Polar : Type := {p : Trit × ℕ // p.1 = Trit.zer ↔ p.2 = 0}

instance : DecidableEq Polar := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- Polarity inversion in polar coordinates: negate the digit, keep the
magnitude. -/
def polarInv (p : Polar) : Polar :=
  ⟨(Trit.inv p.1.1, p.1.2), by
    obtain ⟨⟨t, n⟩, h⟩ := p
    cases t <;> simp [Trit.inv] at h ⊢ <;> simp [h]⟩

/-- The polar-coordinate bijection. -/
def polarEquiv : CentredState ≃ Polar where
  toFun x := ⟨(sideTrit x, orbitMagnitude x), by
    constructor
    · intro h; simpa [orbitMagnitude_eq_zero_iff] using (sideTrit_eq_zer_iff x).1 h
    · intro h; simpa [sideTrit_eq_zer_iff] using (orbitMagnitude_eq_zero_iff x).1 h⟩
  invFun p :=
    match p with
    | ⟨(.zer, _), _⟩ => .criticalCentre
    | ⟨(.neg, n), _⟩ => .offLine .left (n - 1)
    | ⟨(.pos, n), _⟩ => .offLine .right (n - 1)
  left_inv x := by
    cases x with
    | criticalCentre => rfl
    | offLine s n => cases s <;> simp [sideTrit, orbitMagnitude]
  right_inv p := by
    obtain ⟨⟨t, n⟩, h⟩ := p
    cases t
    · have hn : n ≠ 0 := by simpa using fun hn => (h.2 hn)
      have : n - 1 + 1 = n := by omega
      simp [sideTrit, orbitMagnitude, this]
    · have hn : n = 0 := h.1 rfl
      subst hn
      simp [sideTrit, orbitMagnitude]
    · have hn : n ≠ 0 := by simpa using fun hn => (h.2 hn)
      have : n - 1 + 1 = n := by omega
      simp [sideTrit, orbitMagnitude, this]

/-- **Level iv (transport).**  The analytic lane's reflection carrier is the
ternary hub's polarity carrier tensored with a magnitude, and the reflection is
exactly the hub's polarity involution acting on the digit coordinate.  This is
the strongest true statement of the shape the Agda's orbit-shape module gestures
at; the Agda itself identifies no carriers. -/
def centredPolarTransport : Transport CentredState Polar reflect polarInv :=
  ⟨polarEquiv, by
    intro x
    cases x with
    | criticalCentre => rfl
    | offLine s n => cases s <;> rfl⟩

/-! ## 4. The three-phase carrier -/

/-- Mirror of `RiemannReflectionC3OrbitShapeBridgeExact.C3Phase`. -/
inductive C3Phase | identityPhase | zetaPhase | zetaInversePhase
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `invertC3Phase`. -/
def invertC3Phase : C3Phase → C3Phase
  | .identityPhase => .identityPhase
  | .zetaPhase => .zetaInversePhase
  | .zetaInversePhase => .zetaPhase

theorem invertC3Phase_involutive (x : C3Phase) :
    invertC3Phase (invertC3Phase x) = x := by cases x <;> rfl

/-- The three-phase carrier in the hub's balanced coordinate. -/
def c3Equiv : C3Phase ≃ Trit where
  toFun
    | .identityPhase => .zer
    | .zetaPhase => .pos
    | .zetaInversePhase => .neg
  invFun
    | .zer => .identityPhase
    | .pos => .zetaPhase
    | .neg => .zetaInversePhase
  left_inv x := by cases x <;> rfl
  right_inv t := by cases t <;> rfl

/-- **Level iv (transport).**  The analytic lane's `C3Phase` with its inversion
is the corpus's ternary hub carrier with its polarity. -/
def c3Transport : Transport C3Phase Trit invertC3Phase Trit.inv :=
  ⟨c3Equiv, by decide⟩

/-! ## 5. The phases as actual cube roots of unity

The Agda evaluates the phases in a hand-rolled finite cyclotomic model and
proves that the full orbit cancels.  Here the phases are sent to the genuine
primitive cube root of unity of `Spine.TernaryPhase`, and both facts — the
inversion becoming complex conjugation and the vanishing of the orbit sum — are
theorems about `ℂ`. -/

/-- The phase values, in `ℂ`. -/
noncomputable def phaseC : C3Phase → ℂ
  | .identityPhase => 1
  | .zetaPhase => Spine.zeta
  | .zetaInversePhase => Spine.zeta ^ 2

/-- **Level iv (preservation).**  Phase inversion is complex conjugation. -/
theorem phaseC_invert (x : C3Phase) :
    phaseC (invertC3Phase x) = conj (phaseC x) := by
  cases x with
  | identityPhase => simp [phaseC, invertC3Phase]
  | zetaPhase => simpa [phaseC, invertC3Phase] using Spine.conj_zeta.symm
  | zetaInversePhase => simpa [phaseC, invertC3Phase] using Spine.conj_zeta_sq.symm

/-- The complete orbit cancels — over `ℂ`, not in a finite model. -/
theorem phaseC_sum :
    phaseC .identityPhase + phaseC .zetaPhase + phaseC .zetaInversePhase = 0 :=
  Spine.zeta_sum

/-- Each phase is a cube root of unity. -/
theorem phaseC_cube (x : C3Phase) : phaseC x ^ 3 = 1 := by
  cases x with
  | identityPhase => norm_num [phaseC]
  | zetaPhase => simpa [phaseC] using Spine.zeta_cube
  | zetaInversePhase =>
      have : (Spine.zeta ^ 2) ^ 3 = (Spine.zeta ^ 3) ^ 2 := by ring
      simp [phaseC, this, Spine.zeta_cube]

/-- The three phases are distinct complex numbers. -/
theorem phaseC_injective : Function.Injective phaseC := by
  have h1 : Spine.zeta ≠ 1 := Spine.zeta_ne_one
  have h2 : Spine.zeta ^ 2 ≠ 1 := by
    intro h
    refine h1 ?_
    calc Spine.zeta = Spine.zeta * Spine.zeta ^ 2 := by rw [h]; ring
      _ = Spine.zeta ^ 3 := by ring
      _ = 1 := Spine.zeta_cube
  have h3 : Spine.zeta ≠ Spine.zeta ^ 2 := by
    intro h
    refine h2 ?_
    calc Spine.zeta ^ 2 = Spine.zeta * Spine.zeta := by ring
      _ = Spine.zeta * Spine.zeta ^ 2 := by rw [← h]
      _ = Spine.zeta ^ 3 := by ring
      _ = 1 := Spine.zeta_cube
  intro a b hab
  cases a <;> cases b <;> simp only [phaseC] at hab <;>
    first
      | rfl
      | exact absurd hab h1
      | exact absurd hab.symm h1
      | exact absurd hab h2
      | exact absurd hab.symm h2
      | exact absurd hab h3
      | exact absurd hab.symm h3

/-! ## 5b. The Moonshine cyclotomic carrier is a subring of `ℂ`

The *only* cross-domain Agda imports of the whole `Riemann*` lane are
`DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact` (used by the orbit-shape
bridge and by the Maass cross-pollination file), `DASHI.Core.Q` and
`DASHI.TrackedPrimes`.  The Moonshine module represents `a + bζ` by the integer
pair `(a, b)` with `ζ² = -1 - ζ`, and proves the regular-orbit cancellation by
computation in that representation.  Here that representation is *evaluated*:
it is an injective additive map into `ℂ` landing on the actual cube roots of
unity, so the finite model is a faithful picture of the complex phase algebra of
`Spine.TernaryPhase` rather than a separate object. -/

/-- Mirror of `MonsterC3CyclotomicEvaluationExact.Cyclotomic3`: `a + bζ` as an
integer pair. -/
abbrev Cyclotomic3 : Type := ℤ × ℤ

/-- Mirror of `_+c3_`. -/
def addC3 (p q : Cyclotomic3) : Cyclotomic3 := (p.1 + q.1, p.2 + q.2)

/-- Mirror of `phaseValue`. -/
def phaseValueC3 : C3Phase → Cyclotomic3
  | .identityPhase => (1, 0)
  | .zetaPhase => (0, 1)
  | .zetaInversePhase => (-1, -1)

/-- The evaluation `a + bζ ↦ a + b·ζ` into `ℂ`. -/
noncomputable def evalC3 (p : Cyclotomic3) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Spine.zeta

/-- The evaluation is additive. -/
theorem evalC3_add (p q : Cyclotomic3) : evalC3 (addC3 p q) = evalC3 p + evalC3 q := by
  simp [evalC3, addC3]
  ring

/-- **Level iv.**  The evaluation is injective: the Agda's finite cyclotomic
carrier is (isomorphic to) the subring `ℤ[ζ] ⊆ ℂ`. -/
theorem evalC3_injective : Function.Injective evalC3 := by
  intro p q h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [evalC3, Spine.zeta] at him hre
  rw [him] at hre
  have h1 : p.1 = q.1 := by exact_mod_cast (by linarith : ((p.1 : ℝ)) = (q.1 : ℝ))
  exact Prod.ext h1 him

/-- The Agda's `phaseValue` and the complex phases agree under the evaluation. -/
theorem evalC3_phaseValue (x : C3Phase) : evalC3 (phaseValueC3 x) = phaseC x := by
  cases x with
  | identityPhase => simp [evalC3, phaseValueC3, phaseC]
  | zetaPhase => simp [evalC3, phaseValueC3, phaseC]
  | zetaInversePhase =>
      have h := Spine.zeta_sum
      simp only [evalC3, phaseValueC3, phaseC]
      push_cast
      linear_combination -h

/-- The Agda's computational cancellation `completePhaseOrbitCancels`, evaluated:
the orbit sum is zero in `ℂ` as well as in the finite model. -/
theorem evalC3_orbit_cancels :
    evalC3 (addC3 (addC3 (phaseValueC3 .identityPhase) (phaseValueC3 .zetaPhase))
      (phaseValueC3 .zetaInversePhase)) = 0 := by
  rw [evalC3_add, evalC3_add, evalC3_phaseValue, evalC3_phaseValue, evalC3_phaseValue]
  exact phaseC_sum

/-! ## 6. Orbit roles, and where the analogy stops -/

/-- Mirror of `OrbitRole`. -/
inductive OrbitRole | fixedRole | inversePairRole
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `c3OrbitRole`. -/
def c3OrbitRole : C3Phase → OrbitRole
  | .identityPhase => .fixedRole
  | _ => .inversePairRole

/-- Mirror of `zetaOrbitRole`. -/
def centredOrbitRole : CentredState → OrbitRole
  | .criticalCentre => .fixedRole
  | .offLine _ _ => .inversePairRole

theorem c3OrbitRole_invariant (x : C3Phase) :
    c3OrbitRole (invertC3Phase x) = c3OrbitRole x := by cases x <;> rfl

theorem centredOrbitRole_invariant (x : CentredState) :
    centredOrbitRole (reflect x) = centredOrbitRole x := by
  cases x with
  | criticalCentre => rfl
  | offLine s _ => cases s <;> rfl

/-- The reflection carrier is infinite: the magnitude coordinate is unbounded. -/
instance : Infinite CentredState :=
  Infinite.of_injective (fun n : ℕ => CentredState.offLine .left n)
    (by intro a b h; simpa using h)

/-- **Boundary.**  The Agda records `c3AndZetaCarriersIdentified = false` as a
`Bool` field; here it is a theorem.  No bijection whatsoever identifies the
three-phase carrier with the reflection carrier, because the latter is
infinite. -/
theorem c3_not_equiv_centred : ¬ Nonempty (C3Phase ≃ CentredState) := by
  rintro ⟨e⟩
  have : Finite CentredState := Finite.of_equiv _ e
  exact (not_finite CentredState)

/-- **Boundary.**  Neither is the reflection carrier the hub's ternary carrier:
the magnitude survives the polarity classifier.  (Compare
`centredPolarTransport`, which is the corrected statement.) -/
theorem centred_not_equiv_trit : ¬ Nonempty (CentredState ≃ Trit) := by
  rintro ⟨e⟩
  have : Finite CentredState := Finite.of_equiv _ e.symm
  exact (not_finite CentredState)

/-- **Boundary.**  The analogy stops at the orbit-role layer, and this is the
exact reason: the nontrivial role of the reflection carrier has infinitely many
inhabitants (states of every magnitude), whereas the corresponding `C3Phase`
role has two.  The Agda exhibits two examples with different defects; this is
the general statement. -/
theorem inversePair_fibre_infinite :
    Infinite {x : CentredState // centredOrbitRole x = .inversePairRole} :=
  Infinite.of_injective
    (fun n : ℕ => (⟨.offLine .left n, rfl⟩ :
      {x : CentredState // centredOrbitRole x = .inversePairRole}))
    (by intro a b h; simpa [Subtype.ext_iff] using h)

theorem c3_inversePair_fibre_card :
    Fintype.card {x : C3Phase // c3OrbitRole x = .inversePairRole} = 2 := by
  decide

/-- The two role fibres are therefore not in bijection. -/
theorem role_fibres_not_equiv :
    ¬ Nonempty ({x : CentredState // centredOrbitRole x = .inversePairRole} ≃
      {x : C3Phase // c3OrbitRole x = .inversePairRole}) := by
  rintro ⟨e⟩
  have hinf := inversePair_fibre_infinite
  have : Finite {x : CentredState // centredOrbitRole x = .inversePairRole} :=
    Finite.of_equiv _ e.symm
  exact (not_finite {x : CentredState // centredOrbitRole x = .inversePairRole})

end Integration.RiemannReflection
