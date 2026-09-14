import Integration.GaugeSSP

/-!
# Consumers of a symmetric state: invariant, equivariant, gauge-sensitive

A gauge reduction says what the *carrier* does under a symmetry.  This file says
what a **consumer** of the carrier does.  Given an action `act : G → X → X` and
a readout `C : X → β`, exactly one of the following holds for each symmetry
element, and the global classification is a three-way one:

```
Invariant   act C          C (g · x) = C x                     for all g, x
Equivariant act actβ C     C (g · x) = ǧ · C x                 for all g, x
Sensitive   act C          C (g · x) ≠ C x                     for some g, x
```

`Invariant` is the special case of `Equivariant` with the trivial target action,
and `Sensitive` is exactly the negation of `Invariant`.  The point of separating
them is that a state carrying a symmetry usually carries all three kinds of
readout at once, and a reduction is only meaningful relative to which kind of
readout one intends to keep.

Contents:

* `invariant_iff_not_sensitive`, `invariant_iff_equivariant_trivial`,
  `Invariant.comp`, `Equivariant.comp_of_target_invariant` — the structural
  theory;
* `invariant_of_factors` — a consumer factoring through an invariant projection
  is invariant;
* `exists_factor_of_invariant` — conversely, an invariant consumer factors
  through the orbit quotient (the universal property);
* `gauge_consumer_invariant` — for any gauge reduction, every consumer of the
  visible carrier is invariant under the gauge subgroup;
* `ssp_consumer_trichotomy` — on one and the same nine-cell carrier, three
  readouts realise the three classes: the transverse certificate is invariant
  under the whole symmetry, the visible lane is invariant under the gauge
  subgroup but sensitive to the surviving symmetry (and equivariant for the
  coarse action), and the retained wheel-phase residual is already sensitive to
  the gauge subgroup itself.

The finite instances use carriers of at most nine elements; no analytic or
physical claim is made.
-/

namespace Integration.ConsumerGauge

open Integration.Gauge
open Integration.Gauge.GaugeReduction
open Integration.GaugeSSP
open Integration.PhaseQuotient (Phase3)
open Integration.PolarResidual

variable {G X Y β γ : Type*}

/-! ## The three classes -/

/-- The consumer does not see the symmetry at all. -/
def Invariant (act : G → X → X) (C : X → β) : Prop := ∀ g x, C (act g x) = C x

/-- The consumer sees the symmetry, but only through an action on its own
values. -/
def Equivariant (act : G → X → X) (actβ : G → β → β) (C : X → β) : Prop :=
  ∀ g x, C (act g x) = actβ g (C x)

/-- The consumer is moved by the symmetry. -/
def Sensitive (act : G → X → X) (C : X → β) : Prop := ∃ g x, C (act g x) ≠ C x

/-- Invariance and sensitivity are exact complements. -/
theorem invariant_iff_not_sensitive (act : G → X → X) (C : X → β) :
    Invariant act C ↔ ¬ Sensitive act C := by
  unfold Invariant Sensitive
  simp

/-- Invariance is equivariance for the trivial action on values. -/
theorem invariant_iff_equivariant_trivial (act : G → X → X) (C : X → β) :
    Invariant act C ↔ Equivariant act (fun _ b => b) C := Iff.rfl

/-- An equivariant consumer whose target action is trivial is invariant. -/
theorem invariant_of_equivariant_trivial {act : G → X → X} {actβ : G → β → β} {C : X → β}
    (h : Equivariant act actβ C) (htriv : ∀ g b, actβ g b = b) : Invariant act C :=
  fun g x => (h g x).trans (htriv g (C x))

/-- Post-composing an invariant consumer keeps it invariant. -/
theorem Invariant.comp {act : G → X → X} {C : X → β} (h : Invariant act C) (f : β → γ) :
    Invariant act (f ∘ C) := fun g x => congrArg f (h g x)

/-- Post-composing an equivariant consumer with a map that does not see the
target action produces an invariant consumer: this is how a gauge-covariant
quantity is turned into a gauge-invariant one. -/
theorem Equivariant.comp_of_target_invariant {act : G → X → X} {actβ : G → β → β} {C : X → β}
    (h : Equivariant act actβ C) {f : β → γ} (hf : ∀ g b, f (actβ g b) = f b) :
    Invariant act (f ∘ C) := fun g x => by
  simp only [Function.comp_apply, h g x, hf g (C x)]

/-- A consumer that factors through an invariant projection is invariant. -/
theorem invariant_of_factors {act : G → X → X} {π : X → Y} (C : Y → β)
    (hπ : Invariant act π) : Invariant act (C ∘ π) := hπ.comp C

/-- **Universal property.**  An invariant consumer factors through the orbit
quotient, and the factorisation is by the quotient map. -/
theorem exists_factor_of_invariant {act : G → X → X} {C : X → β} (h : Invariant act C) :
    ∃ C' : Quot (fun x y => ∃ g, act g x = y) → β,
      C = C' ∘ Quot.mk (fun x y => ∃ g, act g x = y) := by
  refine ⟨Quot.lift C ?_, rfl⟩
  rintro x y ⟨g, rfl⟩
  exact (h g x).symm

/-- Conversely a consumer of the orbit quotient is always invariant. -/
theorem invariant_of_orbit_consumer (act : G → X → X)
    (C' : Quot (fun x y => ∃ g, act g x = y) → β) :
    Invariant act (C' ∘ Quot.mk (fun x y => ∃ g, act g x = y)) := by
  intro g x
  exact congrArg C' (Quot.sound ⟨g, rfl⟩).symm

/-! ## Gauge reductions -/

variable {G' H Q Rich Coarse : Type} [Monoid G'] [Monoid H] [Monoid Q]

/-- **Every consumer of the visible carrier is gauge-invariant.**  For a gauge
reduction, the gauge subgroup is invisible to the reduced state, hence to
anything computed from it. -/
theorem gauge_consumer_invariant (R : GaugeReduction G' H Q Rich Coarse) (C : Coarse → β) :
    Invariant (fun h x => R.actRich (R.gq.incl h) x) (C ∘ R.red) :=
  fun h x => congrArg C (R.gauge_invariant h x)

/-- The visible carrier is equivariant, not invariant, for the surviving
symmetry: it transforms by the coarse action. -/
theorem red_equivariant (R : GaugeReduction G' H Q Rich Coarse) :
    Equivariant R.actRich (fun g y => R.actCoarse (R.gq.quot g) y) R.red :=
  fun g x => R.square g x

/-- An effective gauge reduction makes the visible carrier a genuinely
symmetry-sensitive consumer of the rich state. -/
theorem red_sensitive_of_effective (R : GaugeReduction G' H Q Rich Coarse)
    (heff : R.Effective) : Sensitive R.actRich R.red :=
  R.effective_not_orbit_quotient heff

/-! ## The three classes realised on one carrier -/

/-- The transverse certificate of the SSP lane is invariant under the whole
`C₃ × C₂` symmetry. -/
theorem ssp_certificate_invariant :
    Invariant actCell sspGaugeObserver.nondegeneracy :=
  fun g c => sspGaugeObserver.nondegeneracy_invariant g c

/-- The visible lane polarity is invariant under the gauge subgroup — the wheel
phase. -/
theorem ssp_lane_gauge_invariant :
    Invariant (fun p c => actCell (sspDatum.incl p) c) (Prod.fst : FullPhaseCell → KernelTrit) :=
  fun p c => ssp_gauge_invariant p c

/-- But the visible lane is sensitive to the surviving polarity flip. -/
theorem ssp_lane_sensitive : Sensitive actCell (Prod.fst : FullPhaseCell → KernelTrit) :=
  ⟨(1, .flip), (.positiveTrit, .phase0), by decide⟩

/-- And the visible lane is equivariant for the coarse polarity action. -/
theorem ssp_lane_equivariant :
    Equivariant actCell (fun g t => sheetOnTrit (sspDatum.quot g) t)
      (Prod.fst : FullPhaseCell → KernelTrit) :=
  fun g c => sspGaugeReduction.square g c

/-- The retained residual — the wheel phase — is already sensitive to the gauge
subgroup: it is precisely the information the reduction discards. -/
theorem ssp_residual_gauge_sensitive :
    Sensitive (fun p c => actCell (sspDatum.incl p) c)
      (Prod.snd : FullPhaseCell → DepthWheelPhase) :=
  ⟨Phase3.p1, (.positiveTrit, .phase0), by decide⟩

/-- **Three readouts of one nine-cell state realise the three classes.**  The
certificate sees no symmetry at all; the visible lane sees only the surviving
`C₂` (invariant under the gauge subgroup, equivariant and sensitive for the full
symmetry); the residual sees the gauge subgroup itself. -/
theorem ssp_consumer_trichotomy :
    Invariant actCell sspGaugeObserver.nondegeneracy ∧
      Invariant (fun p c => actCell (sspDatum.incl p) c)
        (Prod.fst : FullPhaseCell → KernelTrit) ∧
      Equivariant actCell (fun g t => sheetOnTrit (sspDatum.quot g) t)
        (Prod.fst : FullPhaseCell → KernelTrit) ∧
      Sensitive actCell (Prod.fst : FullPhaseCell → KernelTrit) ∧
      Sensitive (fun p c => actCell (sspDatum.incl p) c)
        (Prod.snd : FullPhaseCell → DepthWheelPhase) :=
  ⟨ssp_certificate_invariant, ssp_lane_gauge_invariant, ssp_lane_equivariant,
    ssp_lane_sensitive, ssp_residual_gauge_sensitive⟩

end Integration.ConsumerGauge
