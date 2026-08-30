import Integration.GaugeReduction
import Integration.EquivariantChannel

/-!
# The weld, in the gauge-reduced case

`Integration.StructuredObserver.SymmetryResolvedObserver.symmetry_resolved_theorem`
welds three conclusions — symmetry-compatible coarse dynamics, faithful
fine-state recovery, positive transverse certificate — onto one record.  For a
**gauge** reduction (`Integration.Gauge`) there is a fourth, sharper pair of
statements available: the quotiented subgroup is invisible downstairs, and the
surviving quotient symmetry is not.

`gauge_welded_theorem` states all of them at once for a gauge reduction whose
observer is built through the equivariant-channel constructor — the constructor
one is forced to use exactly when the surviving symmetry moves every class.
-/

namespace Integration.GaugeObserver

open Spine
open Integration.SymmetryReduction
open Integration.StructuredObserver
open Integration.EquivariantChannel
open Integration.Gauge
open Integration.Gauge.GaugeReduction

variable {G H Q Rich Coarse Res K : Type} [Monoid G] [Monoid H] [Monoid Q] [DecidableEq K]
  {n : ℕ} [NeZero n]

/-- **The welded theorem for a gauge reduction.**  A gauge reduction with an
effective surviving symmetry, presented as an observer through an equivariant
transverse channel, yields simultaneously:

1. the observer's visible layer *is* the gauge-reduced carrier;
2. the gauge subgroup is invisible on it;
3. the surviving symmetry is not invisible — it moves the reduced carrier;
4. the rich state is exactly recoverable from visible state plus residual;
5. the transverse certificate is strictly positive; and
6. it is constant along the whole symmetry.

Conclusions 2 and 3 are the gauge/effective dichotomy; 5 and 6 are the spine's
geometry; 4 is the residual-quotient content. -/
theorem gauge_welded_theorem (R : GaugeReduction G H Q Rich Coarse)
    (B : EqObserverBuild G Rich Coarse Res K) (enum : Rich ≃ Fin n)
    (hB : B.reduction = R.toEquivariantQuotient) (heff : R.Effective) :
    (B.toObserver enum).reduction.proj = R.red ∧
      (∀ (h : H) (x : Rich), R.red (R.actRich (R.gq.incl h) x) = R.red x) ∧
      (∃ q y, R.actCoarse q y ≠ y) ∧
      (∀ x, (B.toObserver enum).reopen ((B.toObserver enum).reduction.proj x)
        ((B.toObserver enum).residual x) = x) ∧
      (∀ x, 0 < (B.toObserver enum).nondegeneracy x) ∧
      (∀ g x, (B.toObserver enum).nondegeneracy (B.reduction.actRich g x)
        = (B.toObserver enum).nondegeneracy x) :=
  ⟨by rw [EqObserverBuild.toObserver_reduction, hB]; rfl,
    fun h x => R.gauge_invariant h x,
    heff,
    (B.toObserver enum).fine_recovery,
    (B.toObserver enum).nondegeneracy_pos,
    (B.toObserver enum).nondegeneracy_invariant⟩

/-- The same hypotheses also rule out the reduction being an orbit quotient of
the full symmetry: some symmetry visibly moves the reduced state. -/
theorem gauge_not_orbit_quotient (R : GaugeReduction G H Q Rich Coarse) (heff : R.Effective) :
    ∃ g x, R.red (R.actRich g x) ≠ R.red x :=
  R.effective_not_orbit_quotient heff

end Integration.GaugeObserver
