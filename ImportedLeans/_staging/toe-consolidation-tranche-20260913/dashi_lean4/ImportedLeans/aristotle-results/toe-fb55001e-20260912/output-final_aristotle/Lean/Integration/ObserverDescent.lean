import Integration.StructuredObserver

/-!
# When does the transverse certificate descend to the visible layer?

`SymmetryResolvedObserver.nondegeneracy_invariant` proves the transverse Gram
certificate is constant along the symmetry, hence constant on `G`-orbits.  That
is strictly weaker than being a function of the *visible* state: the projection
`π` may glue together states that no symmetry relates, and then the certificate
is an invariant of the rich carrier only.

This file isolates the exact extra hypothesis under which the gap closes.

* `OrbitFibred O` — every fibre of `π` is contained in a single `G`-orbit.
* `nondegeneracy_descends` — under `OrbitFibred`, the certificate factors
  through `π`: there is a function on the visible layer, `coarseCertificate`,
  with `nondegeneracy x = coarseCertificate (π x)` for every rich state, and it
  is strictly positive.
* `wheelObserver` is orbit-fibred (`wheel_orbitFibred`), so the `C₃` instance's
  certificate is genuinely an observable of the visible layer
  (`wheel_certificate_descends`).
* `ssp369Observer` is **not** (`ssp369_not_orbit_fibred`): its symmetry moves
  between fibres rather than within them, so for that instance the certificate
  remains an invariant of the rich state only.  The two facts together show the
  hypothesis is doing work and is not automatic.
-/

namespace Integration.ObserverDescent

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.PhaseQuotient (Phase3)
open Integration.PolarResidual
open Integration.SSPWeave
open Integration.StructuredObserver

variable {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]

/-- **Fibres are orbits.**  Any two rich states with the same visible state are
related by the symmetry.  This is the condition under which "the coarse layer"
and "the orbit space" agree. -/
def OrbitFibred (O : SymmetryResolvedObserver G Rich Coarse Res n) : Prop :=
  ∀ x y : Rich, O.reduction.proj x = O.reduction.proj y → ∃ g, y = O.reduction.actRich g x

/-- The certificate read off the visible layer, via a section of the (surjective)
projection. -/
noncomputable def coarseCertificate (O : SymmetryResolvedObserver G Rich Coarse Res n)
    (c : Coarse) : ℝ :=
  O.nondegeneracy (Function.surjInv O.reduction.proj_surjective c)

/-- **The certificate descends.**  If the fibres of the projection are orbits,
the transverse Gram certificate is a function of the visible state alone. -/
theorem nondegeneracy_descends (O : SymmetryResolvedObserver G Rich Coarse Res n)
    (horb : OrbitFibred O) (x : Rich) :
    O.nondegeneracy x = coarseCertificate O (O.reduction.proj x) := by
  set s := Function.surjInv O.reduction.proj_surjective (O.reduction.proj x) with hs
  have hproj : O.reduction.proj s = O.reduction.proj x :=
    Function.surjInv_eq O.reduction.proj_surjective _
  obtain ⟨g, hg⟩ := horb s x hproj
  have : O.nondegeneracy x = O.nondegeneracy s := by
    rw [hg]; exact O.nondegeneracy_invariant g s
  simpa [coarseCertificate, ← hs] using this

/-- And the descended certificate is strictly positive on every visible state. -/
theorem coarseCertificate_pos (O : SymmetryResolvedObserver G Rich Coarse Res n)
    (c : Coarse) : 0 < coarseCertificate O c :=
  O.nondegeneracy_pos _

/-- Descent in the packaged form the weld advertises: a positive observable of
the *visible* layer whose pullback is the rich certificate. -/
theorem certificate_is_coarse_observable (O : SymmetryResolvedObserver G Rich Coarse Res n)
    (horb : OrbitFibred O) :
    ∃ F : Coarse → ℝ, (∀ c, 0 < F c) ∧ ∀ x, O.nondegeneracy x = F (O.reduction.proj x) :=
  ⟨coarseCertificate O, coarseCertificate_pos O, nondegeneracy_descends O horb⟩

/-! ## The two instances, on opposite sides of the hypothesis -/

/-- The `C₃` depth-wheel observer is orbit-fibred: two cells with the same lane
polarity differ by a rotation of the wheel. -/
theorem wheel_orbitFibred : OrbitFibred wheelObserver := by
  intro x y h
  have h' : x.1 = y.1 := h
  revert h'
  revert x y
  decide

/-- Hence the `C₃` instance's transverse certificate is an observable of its
visible layer, not merely of the rich state. -/
theorem wheel_certificate_descends :
    ∃ F : KernelTrit → ℝ, (∀ c, 0 < F c) ∧
      ∀ x, wheelObserver.nondegeneracy x = F (wheelObserver.reduction.proj x) :=
  certificate_is_coarse_observable wheelObserver wheel_orbitFibred

/-- **The hypothesis is not automatic.**  The SSP orientation observer is not
orbit-fibred: the orientation flip changes the visible polarity and never the
retained phase, so two cells sharing a polarity but differing in phase lie in one
fibre and in different orbits. -/
theorem ssp369_not_orbit_fibred : ¬ OrbitFibred ssp369Observer := by
  intro h
  obtain ⟨g, hg⟩ :=
    h (KernelTrit.zeroTrit, DepthWheelPhase.phase0) (KernelTrit.zeroTrit, DepthWheelPhase.phase1)
      rfl
  revert hg
  revert g
  decide

end Integration.ObserverDescent
