import Integration.ObserverBundle
import Integration.CoordinateSufficiency
import Integration.MultiscaleDescent
import Integration.PolarResidual

/-!
# A coarse observation with no effective dynamics: the corpus's own projection

`Agda/DASHI/Biology/NeuralRepresentationLaplacianExact.agda` is one of the very
few places in the corpus that supplies an actual *function* from a fine state to
a coarse observation, rather than a `Bool` flag asserting that one exists.  This
file mirrors that function into Lean, checks the two facts the Agda module
proves, and then uses them as the missing consumer for three owners that were
previously exercised only by synthetic carriers:

* `Integration.CoordinateSufficiency` — the coarse observation does not
  determine the fine relational quantity, and this is a *coordinate* statement:
  the discarded distinction is which of two coordinates carries the activity;
* `Integration.ObserverBundle` — the coarse observation puts two distinct fine
  states at measured distance zero, and, more sharply, admits **no** downstream
  transport for one of the fine updates;
* `Integration.MultiscaleDescent` — the same fact, stated as `NoEffectiveLaw`:
  there is no effective law on the coarse observation reproducing the fine one.

## What is and is not claimed

`fmriLikeObservation` is a two-component sum of three natural numbers, named
after the Agda module it mirrors.  It is **not** a model of functional magnetic
resonance imaging, of haemodynamics, or of any measurement device, and
`laplacianVariation` is a sum of truncated natural-number differences, not a
graph Laplacian spectrum.  What is proved is the structural pattern: a
many-to-one observation, an explicit collision, a fine quantity separating the
collided pair, and the consequent non-existence of any effective coarse
description.  Whether a physical measurement has this shape is not addressed
here.

Nothing in this file was typechecked in Agda; it is a Lean transcription of Agda
text, and the Lean side is what is machine-checked.
-/

namespace Integration.NeuralObservation

open Integration.CoordinateSufficiency
open Integration.ObserverBundle
open Integration.MultiscaleDescent

/-! ## The fine state and the two quantities on it -/

/-- Mirror of the Agda `PopulationActivation`: three natural-number
coordinates. -/
structure PopulationActivation where
  /-- First coordinate. -/
  sensory : ℕ
  /-- Second coordinate. -/
  association : ℕ
  /-- Third coordinate. -/
  planning : ℕ
  deriving DecidableEq, Repr

/-- Mirror of the Agda `natDistance`: the symmetrised truncated difference. -/
def natDistance (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- Mirror of the Agda `laplacianVariation`: total variation along the chain of
the three coordinates.  A relational quantity: it depends on the *differences*
between coordinates, not on any one of them. -/
def laplacianVariation (p : PopulationActivation) : ℕ :=
  natDistance p.sensory p.association + natDistance p.association p.planning

theorem uniform_has_zero_variation : laplacianVariation ⟨2, 2, 2⟩ = 0 := rfl

theorem nonuniform_has_finite_variation : laplacianVariation ⟨0, 2, 1⟩ = 3 := rfl

/-! ## The coarse observation -/

/-- Mirror of the Agda `CoarseRegionalObservation`. -/
structure CoarseRegionalObservation where
  /-- The pooled first two coordinates. -/
  anterior : ℕ
  /-- The third coordinate. -/
  posterior : ℕ
  deriving DecidableEq, Repr

/-- Mirror of the Agda `fmriLikeObservation`: pool the first two coordinates. -/
def fmriLikeObservation (p : PopulationActivation) : CoarseRegionalObservation :=
  ⟨p.sensory + p.association, p.planning⟩

/-- The Agda module's two witnesses. -/
def microA : PopulationActivation := ⟨1, 2, 3⟩

/-- The Agda module's two witnesses. -/
def microB : PopulationActivation := ⟨2, 1, 3⟩

theorem microA_ne_microB : microA ≠ microB := by decide

/-- **The collision**, as in the Agda module. -/
theorem fmri_collision : fmriLikeObservation microA = fmriLikeObservation microB := rfl

/-- **And the fine quantity separating the collided pair**, as in the Agda
module. -/
theorem variation_differs :
    laplacianVariation microA = 2 ∧ laplacianVariation microB = 3 := ⟨rfl, rfl⟩

/-! ## Consumer 1: non-factorability -/

/-- **The coarse observation does not determine the relational quantity.** -/
theorem variation_not_determined :
    ¬ Determines fmriLikeObservation laplacianVariation :=
  not_determines_of_collision fmri_collision (by decide)

/-- The same conclusion against every candidate downstream map: there is no
function of the coarse observation equal to the fine quantity. -/
theorem variation_no_downstream_map :
    ¬ Integration.LeastSufficient.Refines fmriLikeObservation laplacianVariation :=
  not_refines_of_collision fmri_collision (by decide)

/-- The fine state read as a three-coordinate product. -/
def coords (p : PopulationActivation) : Fin 3 → ℕ
  | 0 => p.sensory
  | 1 => p.association
  | 2 => p.planning

/-- The relational quantity as a consumer of the coordinate product. -/
def variationOfCoords (x : Fin 3 → ℕ) : ℕ :=
  natDistance (x 0) (x 1) + natDistance (x 1) (x 2)

theorem variationOfCoords_coords (p : PopulationActivation) :
    variationOfCoords (coords p) = laplacianVariation p := rfl

/-- **The coordinate statement.**  Each of the first two coordinates is
essential for the relational quantity, so it factors through no projection that
forgets either of them — while the coarse observation retains only their sum. -/
theorem variation_coords_essential :
    Essential (A := fun _ : Fin 3 => ℕ) 0 variationOfCoords ∧
      Essential (A := fun _ : Fin 3 => ℕ) 1 variationOfCoords := by
  constructor
  · refine ⟨coords ⟨1, 2, 3⟩, coords ⟨0, 2, 3⟩, ?_, by decide⟩
    intro i hi
    fin_cases i <;> simp_all [coords]
  · refine ⟨coords ⟨1, 1, 1⟩, coords ⟨1, 2, 1⟩, ?_, by decide⟩
    intro i hi
    fin_cases i <;> simp_all [coords]

/-! ## Consumer 2: the observer bundle -/

/-- The fine states as a bundle over a one-point base. -/
def activationBundle : Bundle.{0, 0} Unit where
  Total := PopulationActivation
  proj := fun _ => ()

/-- The coarse observation as a real-valued bundle observer. -/
def fmriObserver : BundleObserver activationBundle (ℝ × ℝ) where
  obs := fun p => (((p.sensory + p.association : ℕ) : ℝ), ((p.planning : ℕ) : ℝ))

theorem fmriObserver_collision : fmriObserver.obs microA = fmriObserver.obs microB := by
  simp [fmriObserver, microA, microB]
  norm_num

/-- **Measured distance zero between distinct fine states.**  This is the
corpus-derived consumer of `pullbackDist_self_of_collision`. -/
theorem fmri_pullbackDist_zero : pullbackDist fmriObserver microA microB = 0 :=
  pullbackDist_self_of_collision fmriObserver fmriObserver_collision

/-- Mirror of the Agda `ModulatoryRegime`. -/
inductive ModulatoryRegime
  | inhibited | permissive | recurrent
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `activationUpdate`: the fine law, controlled by a
regime. -/
def activationUpdate : ModulatoryRegime → PopulationActivation → PopulationActivation
  | .inhibited, p => ⟨p.sensory, 0, p.planning⟩
  | .permissive, p => ⟨p.sensory, p.sensory + p.association, p.planning⟩
  | .recurrent, p => ⟨p.sensory, p.sensory + p.association, p.association + p.planning⟩

/-- The Agda module's separation: the same fine state under two regimes. -/
theorem regime_changes_update :
    activationUpdate .inhibited ⟨1, 1, 1⟩ = ⟨1, 0, 1⟩ ∧
      activationUpdate .recurrent ⟨1, 1, 1⟩ = ⟨1, 2, 2⟩ := ⟨rfl, rfl⟩

/-- The recurrent update as a bundle transport. -/
def recurrentTransport : Transport activationBundle where
  move := fun _ _ e => activationUpdate .recurrent e
  move_proj := fun _ _ _ => rfl

/-- **No downstream transport closes the measurement square.**  The observation
identifies `microA` and `microB`, and separates their recurrent updates; so no
map of the coarse observation can be the effective transport. -/
theorem no_effective_transport :
    ∀ Tbar : ℝ × ℝ → ℝ × ℝ, ¬ MeasuredExactly recurrentTransport fmriObserver () () Tbar := by
  refine not_measured_of_collision fmriObserver_collision ?_
  simp [fmriObserver, recurrentTransport, activationUpdate, microA, microB, Prod.ext_iff]

/-! ## Consumer 3: the law does not descend -/

/-- A two-level law tower: the fine population state under the recurrent update,
coarsened by the observation. -/
def neuralTower : LawTower where
  Layer
    | 0 => PopulationActivation
    | 1 => CoarseRegionalObservation
    | _ + 2 => PUnit
  step
    | 0 => fmriLikeObservation
    | 1 => fun _ => PUnit.unit
    | _ + 2 => fun _ => PUnit.unit
  law
    | 0 => activationUpdate .recurrent
    | 1 => id
    | _ + 2 => id

/-- **The strongest negative, from the corpus's own projection.**  There is no
operator on coarse observations at all that reproduces the fine recurrent
update: the failure is a property of the observation, not of a bad choice of
coarse law. -/
theorem neural_no_effective_law : neuralTower.NoEffectiveLaw 0 := by
  rintro ⟨F, hF⟩
  have h1 : fmriLikeObservation (activationUpdate .recurrent microA)
      = F (fmriLikeObservation microA) := hF microA
  have h2 : fmriLikeObservation (activationUpdate .recurrent microB)
      = F (fmriLikeObservation microB) := hF microB
  rw [← fmri_collision] at h2
  exact absurd (h1.trans h2.symm) (by decide)

/-! ## The ternary-phase collision -/

open Integration.PolarResidual (KernelTrit)

/-- Mirror of the Agda `MotifState`. -/
inductive MotifState
  | lattice | tunnel | face | immersiveScene | quiet
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `motifOfTrit`: an injective labelling of the three
phases. -/
def motifOfTrit : KernelTrit → MotifState
  | .negativeTrit => .lattice
  | .zeroTrit => .tunnel
  | .positiveTrit => .face

theorem motifOfTrit_injective : Function.Injective motifOfTrit := by decide

/-- Mirror of the Agda `activationOfTrit`. -/
def activationOfTrit : KernelTrit → PopulationActivation
  | .negativeTrit => microA
  | .zeroTrit => microB
  | .positiveTrit => ⟨2, 2, 2⟩

/-- The coarse observation of a phase. -/
def phaseObservation (t : KernelTrit) : CoarseRegionalObservation :=
  fmriLikeObservation (activationOfTrit t)

/-- **The ternary collision**, as in the Agda module. -/
theorem phase_collision :
    phaseObservation .negativeTrit = phaseObservation .zeroTrit := rfl

theorem phase_variation_differs :
    laplacianVariation (activationOfTrit .negativeTrit) = 2 ∧
      laplacianVariation (activationOfTrit .zeroTrit) = 3 := ⟨rfl, rfl⟩

theorem phase_motifs_differ : motifOfTrit .negativeTrit ≠ motifOfTrit .zeroTrit := by decide

/-- **The coarse observation determines neither the phase nor its motif.**  This
is the corpus's own three-level shape — fine state, coarse projection, hidden
relational label — filed against the generic owner. -/
theorem phase_not_determined :
    ¬ Determines phaseObservation motifOfTrit ∧
      ¬ Determines phaseObservation (id : KernelTrit → KernelTrit) :=
  ⟨not_determines_of_collision phase_collision phase_motifs_differ,
    not_determines_of_collision phase_collision (by decide)⟩

/-- And the motif labelling *is* injective, so the information is present
upstream and destroyed by the projection, not absent to begin with. -/
theorem phase_information_destroyed_not_absent :
    Function.Injective motifOfTrit ∧ ¬ Function.Injective phaseObservation :=
  ⟨motifOfTrit_injective, fun h => absurd (h phase_collision) (by decide)⟩

end Integration.NeuralObservation
