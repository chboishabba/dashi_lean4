/-
# The Gram (Osterwalder–Schrader) positivity mechanism

Reflection positivity of a statistical-mechanical measure is always proved by the
same Fubini computation: the configuration space splits as a product

```
  Ω  ≅  B × A × C          (plane variables, positive variables, negative variables)
```

carrying a product measure, the reflection carries the negative variables onto
the positive ones through a measure-preserving identification `sigma : C ≃ A`
(for gauge theories: relabelling of the links by the reflection, together with
inversion of the reflected link variables), the Boltzmann weight factorises as

```
  D(b, a, c)  =  h(b) · g(a, b) · g(sigma c, b),        h ≥ 0,  g real,
```

and an observable `F` of the positive and plane variables is a function
`f(a, b)`.  Then

```
  ∫ conj (F ∘ Θ) · F · D  =  ∫_B h(b) · ‖∫_A f(a,b) g(a,b) da‖²  ≥  0 .
```

This file proves exactly that, with no unproved input:

* `gramPhi` — the inner `A`-integral `Φ(b) = ∫ f(a,b) g(a,b) da`;
* `gram_integral_eq` — the Fubini identity above;
* `gram_integral_nonneg`, `gram_integral_re_nonneg`, `gram_integral_im` — the
  resulting positivity and reality;
* `ReflectionSplitting` — the same data transported to an abstract configuration
  space through a measure-preserving equivalence, together with
  `ReflectionSplitting.reflection_positive`, the form in which lattice gauge
  theory consumes it.

Nothing here is specific to Yang–Mills; `OS/LinkReflection.lean` builds the
splitting for a lattice gauge configuration space and
`OS/WilsonReflectionPositivity.lean` supplies the literal Wilson instance.
-/
import Mathlib

namespace RequestProject.YangMills.OS

open MeasureTheory Complex

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/-- The Gram vector: the integral of the positive-side observable against the
positive-side factor of the Boltzmann weight, at fixed plane variables. -/
noncomputable def gramPhi (muA : Measure A) (f : A → B → ℂ) (g : A → B → ℝ) (b : B) : ℂ :=
  ∫ a, f a b * (g a b : ℂ) ∂muA

section

variable {muA : Measure A} {muB : Measure B} {muC : Measure C}
  [SFinite muA] [SFinite muB] [SFinite muC]
  {f : A → B → ℂ} {g : A → B → ℝ} {h : B → ℝ} {sigma : C ≃ᵐ A}

/-- The reflected pairing of a positive-side observable with itself against a
factorising density. -/
noncomputable def gramPairing (muA : Measure A) (muB : Measure B) (muC : Measure C)
    (f : A → B → ℂ) (g : A → B → ℝ) (h : B → ℝ) (sigma : C ≃ᵐ A) : ℂ :=
  ∫ w : B × A × C, (starRingEnd ℂ) (f (sigma w.2.2) w.1) * f w.2.1 w.1 *
    ((h w.1 : ℂ) * (g w.2.1 w.1 : ℂ) * (g (sigma w.2.2) w.1 : ℂ)) ∂(muB.prod (muA.prod muC))

/-- The integrand of `gramPairing`. -/
noncomputable def gramIntegrand (f : A → B → ℂ) (g : A → B → ℝ) (h : B → ℝ) (sigma : C ≃ᵐ A) :
    B × A × C → ℂ :=
  fun w => (starRingEnd ℂ) (f (sigma w.2.2) w.1) * f w.2.1 w.1 *
    ((h w.1 : ℂ) * (g w.2.1 w.1 : ℂ) * (g (sigma w.2.2) w.1 : ℂ))

omit [SFinite muA] [SFinite muB] [SFinite muC] in
theorem gramPairing_eq_integral :
    gramPairing muA muB muC f g h sigma
      = ∫ w, gramIntegrand f g h sigma w ∂(muB.prod (muA.prod muC)) := rfl

/-- **The Gram identity.**  The reflected pairing is the `B`-integral of
`h · ‖Φ‖²`; in particular it is real and nonnegative. -/
theorem gram_integral_eq (hsigma : MeasurePreserving sigma muC muA)
    (hint : Integrable (gramIntegrand f g h sigma) (muB.prod (muA.prod muC))) :
    gramPairing muA muB muC f g h sigma
      = ((∫ b, h b * ‖gramPhi muA f g b‖ ^ 2 ∂muB : ℝ) : ℂ) := by
  rw [gramPairing_eq_integral, integral_prod _ hint]
  have key : ∀ b : B, ∫ p : A × C, gramIntegrand f g h sigma (b, p) ∂(muA.prod muC)
      = ((h b * ‖gramPhi muA f g b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    have hre : ∀ p : A × C, gramIntegrand f g h sigma (b, p)
        = ((fun a => (h b : ℂ) * (f a b * (g a b : ℂ))) p.1) *
           ((fun c => (starRingEnd ℂ) (f (sigma c) b) * (g (sigma c) b : ℂ)) p.2) := by
      intro p; simp only [gramIntegrand]; ring
    simp_rw [hre]
    rw [integral_prod_mul (fun a => (h b : ℂ) * (f a b * (g a b : ℂ)))
      (fun c => (starRingEnd ℂ) (f (sigma c) b) * (g (sigma c) b : ℂ))]
    have h1 : ∫ a, (h b : ℂ) * (f a b * (g a b : ℂ)) ∂muA = (h b : ℂ) * gramPhi muA f g b := by
      rw [integral_const_mul]; rfl
    have h2 : ∫ c, (starRingEnd ℂ) (f (sigma c) b) * (g (sigma c) b : ℂ) ∂muC
        = (starRingEnd ℂ) (gramPhi muA f g b) := by
      have hc := hsigma.integral_comp sigma.measurableEmbedding
        (fun a => (starRingEnd ℂ) (f a b) * (g a b : ℂ))
      rw [hc, gramPhi, ← integral_conj]
      simp
    rw [h1, h2, mul_assoc, Complex.mul_conj']
    push_cast
    ring
  simp_rw [key]
  rw [integral_complex_ofReal]

omit [SFinite muA] [SFinite muB] in
/-- The Gram integrand is nonnegative when the plane weight is. -/
theorem gram_integral_nonneg (hh : ∀ b, 0 ≤ h b) :
    0 ≤ ∫ b, h b * ‖gramPhi muA f g b‖ ^ 2 ∂muB :=
  integral_nonneg fun b => mul_nonneg (hh b) (sq_nonneg _)

/-- **Reflection positivity in coordinates**: the reflected pairing has
nonnegative real part. -/
theorem gram_integral_re_nonneg (hsigma : MeasurePreserving sigma muC muA) (hh : ∀ b, 0 ≤ h b)
    (hint : Integrable (gramIntegrand f g h sigma) (muB.prod (muA.prod muC))) :
    0 ≤ (gramPairing muA muB muC f g h sigma).re := by
  rw [gram_integral_eq hsigma hint]
  simpa using gram_integral_nonneg (muA := muA) (muB := muB) (f := f) (g := g) hh

/-- The reflected pairing is real. -/
theorem gram_integral_im (hsigma : MeasurePreserving sigma muC muA)
    (hint : Integrable (gramIntegrand f g h sigma) (muB.prod (muA.prod muC))) :
    (gramPairing muA muB muC f g h sigma).im = 0 := by
  rw [gram_integral_eq hsigma hint]
  simp

end

/-! ## The same data on an abstract configuration space -/

/-- A **reflection splitting** of a measure space: a measure-preserving
identification of the configuration space with a product

```
  plane variables × positive variables × negative variables
```

together with a reflection whose plane coordinate is the identity and whose
positive coordinate is a measure-preserving image of the negative coordinate. -/
structure ReflectionSplitting (Omega : Type*) [MeasurableSpace Omega] (mu0 : Measure Omega)
    (A B C : Type*) [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] where
  /-- The coordinates: plane, positive, negative. -/
  coord : Omega ≃ᵐ B × A × C
  /-- The measure on the positive variables. -/
  muA : Measure A
  /-- The measure on the plane variables. -/
  muB : Measure B
  /-- The measure on the negative variables. -/
  muC : Measure C
  /-- s-finiteness of the positive factor. -/
  sfiniteA : SFinite muA
  /-- s-finiteness of the plane factor. -/
  sfiniteB : SFinite muB
  /-- s-finiteness of the negative factor. -/
  sfiniteC : SFinite muC
  /-- The coordinates carry the measure to the product measure. -/
  coord_mp : MeasurePreserving coord mu0 (muB.prod (muA.prod muC))
  /-- The reflection of configurations. -/
  refl : Omega → Omega
  /-- The identification of the negative with the positive variables. -/
  sigma : C ≃ᵐ A
  /-- It is measure preserving. -/
  sigma_mp : MeasurePreserving sigma muC muA
  /-- The reflection does not move the plane variables. -/
  plane_refl : ∀ w : Omega, (coord (refl w)).1 = (coord w).1
  /-- The positive variables of the reflected configuration are the image of the
  negative variables of the original one. -/
  pos_refl : ∀ w : Omega, (coord (refl w)).2.1 = sigma (coord w).2.2

namespace ReflectionSplitting

variable {Omega : Type*} [MeasurableSpace Omega] {mu0 : Measure Omega}
  (S : ReflectionSplitting Omega mu0 A B C)

/-- The plane coordinate of a configuration. -/
def plane (w : Omega) : B := (S.coord w).1

/-- The positive coordinate of a configuration. -/
def pos (w : Omega) : A := (S.coord w).2.1

/-- The negative coordinate of a configuration. -/
def neg (w : Omega) : C := (S.coord w).2.2

/-- **Reflection positivity on the configuration space.**  If the observable `F`
is a function of the positive and plane variables, and the density `D`
factorises as `h(plane) · g(pos, plane) · g(pos of the reflected configuration,
plane)`, then the reflected pairing of `F` with itself is real and
nonnegative. -/
theorem reflection_positive {F : Omega → ℂ} {D : Omega → ℝ}
    {f : A → B → ℂ} {g : A → B → ℝ} {h : B → ℝ}
    (hF : ∀ w, F w = f (S.pos w) (S.plane w))
    (hD : ∀ w, D w = h (S.plane w) * g (S.pos w) (S.plane w) * g (S.pos (S.refl w)) (S.plane w))
    (hh : ∀ b, 0 ≤ h b)
    (hint : Integrable (gramIntegrand f g h S.sigma) (S.muB.prod (S.muA.prod S.muC))) :
    0 ≤ (∫ w, (starRingEnd ℂ) (F (S.refl w)) * F w * (D w : ℂ) ∂mu0).re ∧
      (∫ w, (starRingEnd ℂ) (F (S.refl w)) * F w * (D w : ℂ) ∂mu0).im = 0 := by
  haveI := S.sfiniteA
  haveI := S.sfiniteB
  haveI := S.sfiniteC
  have hpos_refl : ∀ w : Omega, S.pos (S.refl w) = S.sigma (S.neg w) := S.pos_refl
  have hplane_refl : ∀ w : Omega, S.plane (S.refl w) = S.plane w := S.plane_refl
  have hrw : ∀ w : Omega, (starRingEnd ℂ) (F (S.refl w)) * F w * (D w : ℂ)
      = gramIntegrand f g h S.sigma (S.coord w) := by
    intro w
    rw [hF w, hF (S.refl w), hD w, hplane_refl w, hpos_refl w]
    simp only [gramIntegrand, plane, pos, neg]
    push_cast
    ring
  have hint2 : ∫ w, (starRingEnd ℂ) (F (S.refl w)) * F w * (D w : ℂ) ∂mu0
      = gramPairing S.muA S.muB S.muC f g h S.sigma := by
    rw [gramPairing_eq_integral]
    simp_rw [hrw]
    exact S.coord_mp.integral_comp S.coord.measurableEmbedding (gramIntegrand f g h S.sigma)
  rw [hint2]
  exact ⟨gram_integral_re_nonneg S.sigma_mp hh hint, gram_integral_im S.sigma_mp hint⟩

end ReflectionSplitting

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms gram_integral_eq
#print axioms gram_integral_re_nonneg
#print axioms ReflectionSplitting.reflection_positive

end Audit
