import Integration.ConsumerGauge
import Integration.StructureMorphism

/-!
# The first non-finite gauge instance: a global `U(1)` phase

Every gauge instance in this tree so far has a finite carrier and a finite
symmetry group (`Integration.GaugeSU2`, `Integration.GaugeSSP`).  That is a real
ceiling: the consumer classification of `Integration.ConsumerGauge` was only
ever exercised against finite data.  This file breaks the ceiling with the
smallest genuinely continuous case, a global phase acting on a complex inner
product space:

```
u • x = (u : ℂ) • x,      u ∈ Circle = { z : ℂ  ‖z‖ = 1 }.
```

The group is infinite and compact, the carrier is infinite dimensional in
general, and nothing here is finite.

What the file proves.

* `phaseAct`, `phaseAct_one`, `phaseAct_mul` — the action;
* **invariant** readouts: the norm (`norm_invariant`), and — the fact that welds
  this to the Gram/certificate lane — the *whole Hermitian form*
  (`inner_invariant`): a Gram entry between two states transported by the same
  phase is unchanged.  Every quadratic/Gram certificate built from it is
  therefore gauge invariant (`gram_certificate_invariant`);
* **equivariant** readouts: the state itself (`state_equivariant`) and any
  continuous-linear channel out of it (`channel_equivariant`), with the target
  action being the same phase multiplication;
* **gauge-sensitive** readouts: the raw phase coordinate `Complex.arg`
  (`arg_sensitive`), and the raw amplitude, which is equivariant but not
  invariant (`state_sensitive`);
* `u1_consumer_trichotomy` — the three classes realised simultaneously on `ℂ`;
* `norm_complete_invariant` — the norm is a *complete* invariant of the phase
  orbit on `ℂ`: `‖z‖ = ‖w‖ ↔ ∃ u, w = u • z`.  So the orbit quotient of the
  phase action on `ℂ` is exactly the norm, and the universal property of
  `Integration.ConsumerGauge.exists_factor_of_invariant` is realised by an
  explicit map rather than a choice;
* `phaseResidual`, `reopen_phase` — the **reconstructive residual** for this
  gauge: modulus together with the retained phase reopens the state exactly,
  and `no_retraction_without_residual` shows the residual is not removable;
* `phaseGauge` — the whole thing packaged as a
  `Integration.Gauge.GaugeReduction` with gauge group the full circle and
  surviving symmetry trivial, together with `phaseGauge_exact`; by the corpus's
  own `coarse_action_trivial_of_orbit` this is the orbit-quotient case, so the
  surviving action *must* be trivial — recorded here rather than assumed.

No physical claim is made: `Circle` is the unit circle in `ℂ`, and no statement
here concerns electromagnetism, a wavefunction, or any measured quantity.
-/

namespace Integration.PhaseGaugeU1

open Integration.ConsumerGauge
open Integration.Gauge
open Integration.StructureMorphism

/-! ## The action -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The global phase action of the circle group on a complex inner product
space. -/
def phaseAct (u : Circle) (x : V) : V := (u : ℂ) • x

@[simp] theorem phaseAct_apply (u : Circle) (x : V) : phaseAct u x = (u : ℂ) • x := rfl

@[simp] theorem phaseAct_one (x : V) : phaseAct (1 : Circle) x = x := by
  simp [phaseAct]

theorem phaseAct_mul (u v : Circle) (x : V) :
    phaseAct (u * v) x = phaseAct u (phaseAct v x) := by
  simp [phaseAct, mul_smul]

/-- The conjugate–times–itself identity that drives every invariance below. -/
theorem conj_mul_self (u : Circle) : (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = 1 := by
  have h : Complex.normSq (u : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]; ring
  rw [mul_comm, Complex.mul_conj, h]; norm_num

/-! ## Invariant readouts -/

/-- **The norm is gauge invariant.** -/
theorem norm_invariant : Invariant (phaseAct (V := V)) (fun x => ‖x‖) := by
  intro u x
  simp [phaseAct, norm_smul]

/-- **The Hermitian form is gauge invariant** under the *simultaneous* phase.
This is the weld to the certificate lane: a Gram entry does not see a global
phase. -/
theorem inner_invariant (u : Circle) (x y : V) :
    (inner ℂ (phaseAct u x) (phaseAct u y) : ℂ) = inner ℂ x y := by
  rw [phaseAct_apply, phaseAct_apply, inner_smul_left, inner_smul_right, ← mul_assoc,
    conj_mul_self, one_mul]

/-- Hence every quantity built from Gram entries of a simultaneously transported
family is gauge invariant. -/
theorem gram_certificate_invariant {ι : Type*} [Fintype ι] (u : Circle) (v : ι → V)
    (F : Matrix ι ι ℂ → ℂ) :
    F (Matrix.of fun i j => (inner ℂ (phaseAct u (v i)) (phaseAct u (v j)) : ℂ))
      = F (Matrix.of fun i j => (inner ℂ (v i) (v j) : ℂ)) := by
  congr 1
  ext i j
  exact inner_invariant u (v i) (v j)

/-! ## Equivariant readouts -/

/-- **The state itself is equivariant**, for the phase action on the target. -/
theorem state_equivariant :
    Equivariant (phaseAct (V := V)) (phaseAct (V := V)) (fun x => x) := fun _ _ => rfl

/-- **Any linear channel is equivariant**, with the target action being scalar
multiplication by the same phase. -/
theorem channel_equivariant {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (L : V →ₗ[ℂ] W) :
    Equivariant (phaseAct (V := V)) (phaseAct (V := W)) (fun x => L x) := by
  intro u x
  simp [phaseAct, map_smul]

/-! ## Gauge-sensitive readouts -/

/-- The half-turn, as an element of the circle group. -/
def half : Circle := ⟨-1, by
  simp [Submonoid.unitSphere, mem_sphere_iff_norm]⟩

@[simp] theorem half_coe : ((half : Circle) : ℂ) = -1 := rfl

/-- **The raw phase coordinate is gauge sensitive.** -/
theorem arg_sensitive : Sensitive (phaseAct (V := ℂ)) Complex.arg := by
  refine ⟨half, 1, ?_⟩
  simp [phaseAct]

/-- The raw amplitude is sensitive too — being equivariant does not make a
readout invariant. -/
theorem state_sensitive : Sensitive (phaseAct (V := ℂ)) (fun z => z) := by
  refine ⟨half, 1, ?_⟩
  simp only [phaseAct_apply, half_coe, smul_eq_mul, mul_one]
  norm_num

/-- **The trichotomy on one carrier.**  On `ℂ` with the global phase action, the
modulus is invariant, the state is equivariant and sensitive, and the raw phase
is sensitive.  Continuous group, infinite carrier. -/
theorem u1_consumer_trichotomy :
    Invariant (phaseAct (V := ℂ)) (fun z => ‖z‖) ∧
      Equivariant (phaseAct (V := ℂ)) (phaseAct (V := ℂ)) (fun z => z) ∧
      Sensitive (phaseAct (V := ℂ)) (fun z => z) ∧
      Sensitive (phaseAct (V := ℂ)) Complex.arg :=
  ⟨norm_invariant, state_equivariant, state_sensitive, arg_sensitive⟩

/-! ## The orbit quotient is exactly the modulus -/

/-- **The modulus is a complete invariant of the phase orbit.**  So on `ℂ` the
factorisation guaranteed abstractly by
`Integration.ConsumerGauge.exists_factor_of_invariant` is realised by the
explicit map `‖·‖`, and no finer invariant is gauge invariant. -/
theorem norm_complete_invariant (z w : ℂ) : ‖z‖ = ‖w‖ ↔ ∃ u : Circle, w = phaseAct u z := by
  constructor
  · intro h
    rcases eq_or_ne z 0 with rfl | hz
    · refine ⟨1, ?_⟩
      simp only [norm_zero] at h
      simp [phaseAct, (norm_eq_zero.mp h.symm)]
    · have hw : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h
        exact hz (norm_eq_zero.mp h)
      refine ⟨⟨w / z, ?_⟩, ?_⟩
      · simp [Submonoid.unitSphere, Metric.sphere, h, hw]
      · show w = (w / z : ℂ) • z
        rw [smul_eq_mul]
        field_simp
  · rintro ⟨u, rfl⟩
    exact (norm_invariant u z).symm

/-! ## The reconstructive residual -/

/-- The retained phase of a complex number (the unit at `0` is a convention; the
reopening identity below holds at `0` as well). -/
noncomputable def phaseResidual (z : ℂ) : Circle :=
  if h : z = 0 then 1 else ⟨z / (‖z‖ : ℂ), by
    simp [Submonoid.unitSphere, Metric.sphere, h]⟩

/-- **Modulus plus retained phase reopens the state exactly.**  This is the
reconstructive residual law for the phase gauge. -/
theorem reopen_phase (z : ℂ) : phaseAct (phaseResidual z) (‖z‖ : ℂ) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [phaseResidual, phaseAct]
  · have hnz : (‖z‖ : ℂ) ≠ 0 := by
      simpa using hz
    simp only [phaseResidual, dif_neg hz, phaseAct_apply]
    show (z / (‖z‖ : ℂ)) * (‖z‖ : ℂ) = z
    field_simp

/-- **The residual is not removable.**  No function of the modulus alone can
recover the state: two distinct states share a modulus. -/
theorem no_retraction_without_residual :
    ¬ ∃ s : ℝ → ℂ, ∀ z : ℂ, s ‖z‖ = z := by
  rintro ⟨s, hs⟩
  have h1 := hs 1
  have h2 := hs (-1)
  rw [show ‖(1 : ℂ)‖ = 1 by simp] at h1
  rw [show ‖(-1 : ℂ)‖ = 1 by simp, h1] at h2
  exact absurd h2 (by norm_num)

/-! ## Packaged as a gauge reduction -/

/-- The phase gauge as a `GaugeReduction`: the whole circle is the gauge group,
the surviving symmetry is trivial, and the visible carrier is the modulus. -/
noncomputable def phaseGauge : GaugeReduction Circle Circle Unit ℂ NNReal where
  gq :=
    { incl := id
      incl_one := rfl
      incl_mul := fun _ _ => rfl
      quot := fun _ => ()
      quot_one := rfl
      quot_mul := fun _ _ => rfl
      quot_surjective := fun _ => ⟨1, rfl⟩
      quot_incl := fun _ => rfl }
  actRich := phaseAct
  rich_one := phaseAct_one
  rich_mul := phaseAct_mul
  actCoarse := fun _ r => r
  coarse_one := fun _ => rfl
  coarse_mul := fun _ _ _ => rfl
  red := fun z => ‖z‖₊
  red_surjective := by
    intro r
    exact ⟨(r : ℝ), by simp⟩
  square := by
    intro u x
    show ‖phaseAct u x‖₊ = ‖x‖₊
    ext
    exact norm_invariant u x

/-- The gauge datum is exact: the kernel of the (trivial) effective quotient is
exactly the gauge group. -/
theorem phaseGauge_exact : phaseGauge.gq.Exact := fun g _ => ⟨g, rfl⟩

/-- Because the gauge group is the *whole* symmetry, this is an orbit quotient
and the surviving action is forced to be trivial — the corpus's own
`coarse_action_trivial_of_orbit`, realised on a continuous group. -/
theorem phaseGauge_coarse_trivial (q : Unit) (r : NNReal) :
    phaseGauge.actCoarse q r = r := rfl

/-- The phase gauge is an instance of the single commuting-square owner. -/
theorem phaseGauge_structureMorphism :
    Gauge phaseGauge.gq.quot phaseGauge.actRich phaseGauge.actCoarse phaseGauge.red :=
  gauge_of_gaugeReduction phaseGauge

end Integration.PhaseGaugeU1
