import Integration.StructuredObserver

/-!
# Towers: the hierarchy `raw → reduced → coarser` composes

`Integration.StructuredObserver` welds the spine's geometry to the integration
layer's transport in a single record, and inhabits it four times.  Each
inhabitant is a *single* arrow `Rich → Coarse`.  The intended picture, however,
is a hierarchy

```
raw carrier  --symmetry reduction-->  reduced carrier  --observer-->  coarser carrier
```

with a different theorem obligation on each arrow.  This file proves that the
hierarchy is closed under composition, so the picture is one object rather than
a diagram drawn by hand.

* `compQuotient` — two equivariant quotients for the *same* symmetry, whose
  middle actions agree, compose to an equivariant quotient.  Surjectivity,
  unitality, multiplicativity and the commuting square all compose.
* `towerOf` — a symmetry-resolved observer, followed by a
  further equivariant quotient of its coarse layer carrying its own reopenable
  residual, is again a symmetry-resolved observer, whose residual is the *pair*
  of residuals.  The representation, reading and channel are carried through
  unchanged.
* `tower_nondegeneracy` — consequently the transverse certificate is **exactly
  preserved** by descending one more level: coarsening the visible layer cannot
  manufacture or destroy transverse volume, because the certificate is a
  function of the rich state and the chosen chart alone.  (`tower_theorem`
  bundles this with the three welded conclusions for the composite.)
* `tower_card_bound` — the residual grows multiplicatively down the tower:
  what the coarser layer stops showing must be paid for in retained residual.

The concrete tower is the SSP nine-cell lane, reduced twice:

```
9 full phase cells  --orientation-->  3 kernel trits  --magnitude-->  2 magnitudes
```

with residual `sign × phase` of size six (`sspTower`, `sspTower_cards`).  The
second stage is a genuine further reduction — its upstairs action is the
nontrivial trit negation, its downstairs action is trivial — so the tower is not
a reduction followed by an isomorphism.
-/

namespace Integration.ObserverTower

open Spine
open Spine.MeanSplit
open Integration.SymmetryReduction
open Integration.Residual
open Integration.PolarResidual
open Integration.SSPWeave
open Integration.StructuredObserver

/-! ## Composition of equivariant quotients -/

variable {G Rich Mid Coarse : Type} [Monoid G]

/-- **Equivariant quotients compose.**  If `Q : Rich ↠ Mid` and `P : Mid ↠ Coarse`
are equivariant for the same symmetry and their two actions on the middle layer
agree, then `P ∘ Q` is an equivariant quotient. -/
def compQuotient (Q : EquivariantQuotient G Rich Mid) (P : EquivariantQuotient G Mid Coarse)
    (hmid : ∀ g y, P.actRich g y = Q.actCoarse g y) :
    EquivariantQuotient G Rich Coarse where
  actRich := Q.actRich
  actCoarse := P.actCoarse
  proj := fun x => P.proj (Q.proj x)
  rich_one := Q.rich_one
  rich_mul := Q.rich_mul
  coarse_one := P.coarse_one
  coarse_mul := P.coarse_mul
  proj_surjective := P.proj_surjective.comp Q.proj_surjective
  square := fun g x => by
    show P.proj (Q.proj (Q.actRich g x)) = P.actCoarse g (P.proj (Q.proj x))
    rw [Q.square, ← hmid, P.square]

@[simp] theorem compQuotient_proj (Q : EquivariantQuotient G Rich Mid)
    (P : EquivariantQuotient G Mid Coarse) (hmid : ∀ g y, P.actRich g y = Q.actCoarse g y)
    (x : Rich) : (compQuotient Q P hmid).proj x = P.proj (Q.proj x) := rfl

@[simp] theorem compQuotient_actRich (Q : EquivariantQuotient G Rich Mid)
    (P : EquivariantQuotient G Mid Coarse) (hmid : ∀ g y, P.actRich g y = Q.actCoarse g y)
    (g : G) (x : Rich) : (compQuotient Q P hmid).actRich g x = Q.actRich g x := rfl

/-! ## Composition of symmetry-resolved observers -/

/-- The data needed to extend a symmetry-resolved observer by one more level: an
equivariant quotient of its coarse layer, agreeing with the induced action, and
carrying its own reopenable residual. -/
structure Extension (G Mid Coarse Res : Type) [Monoid G]
    (actMid : G → Mid → Mid) where
  /-- The further reduction of the visible layer. -/
  step : EquivariantQuotient G Mid Coarse
  /-- Its action upstairs is the one already induced on the middle layer. -/
  step_action : ∀ g y, step.actRich g y = actMid g y
  /-- The residual retained by the further reduction. -/
  residual : Mid → Res
  /-- Its reassembly map. -/
  reopen : Coarse → Res → Mid
  /-- Reassembly is exact, so the further reduction is lossless too. -/
  reopen_project : ∀ y, reopen (step.proj y) (residual y) = y

variable {Res Res₂ : Type} {n : ℕ} [NeZero n]
  (O : SymmetryResolvedObserver G Rich Mid Res n)

/-- **The hierarchy composes.**  A symmetry-resolved observer followed by an
extension of its visible layer is again a symmetry-resolved observer, with the
pair of residuals as its residual and the *same* representation, reading and
channel. -/
def towerOf (E : Extension G Mid Coarse Res₂ O.reduction.actCoarse) :
    SymmetryResolvedObserver G Rich Coarse (Res₂ × Res) n where
  reduction := compQuotient O.reduction E.step E.step_action
  residual := fun x => (E.residual (O.reduction.proj x), O.residual x)
  reopen := fun c p => O.reopen (E.reopen c p.1) p.2
  reopen_project := fun x => by
    show O.reopen (E.reopen (E.step.proj (O.reduction.proj x))
      (E.residual (O.reduction.proj x))) (O.residual x) = x
    rw [E.reopen_project, O.reopen_project]
  rep := O.rep
  read := O.read
  channel := O.channel
  read_equivariant := O.read_equivariant
  channel_equivariant := O.channel_equivariant
  mean_ne_zero := O.mean_ne_zero
  fluct_ne_zero := O.fluct_ne_zero

/-- **The certificate survives the extra level exactly.**  Descending one more
step in the hierarchy neither creates nor destroys transverse volume: the
nondegeneracy certificate of the tower is the certificate of its first stage. -/
@[simp] theorem tower_nondegeneracy (E : Extension G Mid Coarse Res₂ O.reduction.actCoarse)
    (x : Rich) : (towerOf O E).nondegeneracy x = O.nondegeneracy x := rfl

/-- The tower's visible layer is the composite projection. -/
@[simp] theorem tower_proj (E : Extension G Mid Coarse Res₂ O.reduction.actCoarse) (x : Rich) :
    (towerOf O E).reduction.proj x = E.step.proj (O.reduction.proj x) := rfl

/-- The tower retains both residuals. -/
@[simp] theorem tower_residual (E : Extension G Mid Coarse Res₂ O.reduction.actCoarse)
    (x : Rich) :
    (towerOf O E).residual x = (E.residual (O.reduction.proj x), O.residual x) := rfl

/-- **The tower theorem.**  The composite satisfies the three welded conclusions,
and its certificate is the one already proved for the first stage. -/
theorem tower_theorem (E : Extension G Mid Coarse Res₂ O.reduction.actCoarse) :
    (Function.Surjective (towerOf O E).reduction.proj ∧
        ∀ g x, (towerOf O E).reduction.proj ((towerOf O E).reduction.actRich g x)
          = (towerOf O E).reduction.actCoarse g ((towerOf O E).reduction.proj x)) ∧
      (∀ x, (towerOf O E).reopen ((towerOf O E).reduction.proj x)
        ((towerOf O E).residual x) = x) ∧
      Function.Injective
        (fun x => ((towerOf O E).reduction.proj x, (towerOf O E).residual x)) ∧
      (∀ x, 0 < (towerOf O E).nondegeneracy x) ∧
      (∀ g x, (towerOf O E).nondegeneracy ((towerOf O E).reduction.actRich g x)
        = (towerOf O E).nondegeneracy x) ∧
      (∀ x, (towerOf O E).nondegeneracy x = O.nondegeneracy x) :=
  ⟨⟨(towerOf O E).coarse_surjective, (towerOf O E).coarse_dynamics⟩,
    (towerOf O E).fine_recovery, (towerOf O E).coarse_residual_injective,
    (towerOf O E).nondegeneracy_pos, (towerOf O E).nondegeneracy_invariant,
    fun x => tower_nondegeneracy O E x⟩

/-- **What the coarser layer stops showing is paid for in residual.**  The rich
carrier embeds into `visible × (new residual × old residual)`, so descending one
more level forces the retained residual to grow by at least the factor the
visible layer lost. -/
theorem tower_card_bound [Fintype Rich] [Fintype Coarse] [Fintype Res] [Fintype Res₂]
    (E : Extension G Mid Coarse Res₂ O.reduction.actCoarse) :
    Fintype.card Rich ≤ Fintype.card Coarse * (Fintype.card Res₂ * Fintype.card Res) := by
  have h := Fintype.card_le_of_injective _ (towerOf O E).coarse_residual_injective
  simpa [Fintype.card_prod] using h

/-! ## The concrete tower: `9 → 3 → 2` on the SSP nine-cell lane -/

/-- The magnitude of a kernel trit: `true` exactly at the zero state.  This is
the polarity-invariant Boolean observer of the ternary hub. -/
def kernelMagnitude : KernelTrit → Bool
  | .zeroTrit => true
  | _ => false

/-- The sign residual of a kernel trit. -/
def kernelSign : KernelTrit → Bool
  | .negativeTrit => true
  | _ => false

/-- Reassembly of a kernel trit from magnitude and sign. -/
def kernelReopen : Bool → Bool → KernelTrit
  | true, _ => .zeroTrit
  | false, true => .negativeTrit
  | false, false => .positiveTrit

theorem kernelReopen_project (t : KernelTrit) :
    kernelReopen (kernelMagnitude t) (kernelSign t) = t := by
  cases t <;> rfl

/-- **The second stage.**  The magnitude observer `3 → 2` is equivariant for the
orientation action, with trivial induced action: negation preserves magnitude.
Its residual is the sign, and magnitude together with sign reopens the trit. -/
def magnitudeStep : EquivariantQuotient FibreOrientation KernelTrit Bool where
  actRich := actKernel
  actCoarse := fun _ b => b
  proj := kernelMagnitude
  rich_one := fun t => by cases t <;> rfl
  rich_mul := by decide
  coarse_one := fun _ => rfl
  coarse_mul := fun _ _ _ => rfl
  proj_surjective := by decide
  square := by decide

/-- The magnitude observer as an extension of the SSP 369 observer. -/
def magnitudeExtension :
    Extension FibreOrientation KernelTrit Bool Bool ssp369Observer.reduction.actCoarse where
  step := magnitudeStep
  step_action := fun _ _ => rfl
  residual := kernelSign
  reopen := kernelReopen
  reopen_project := kernelReopen_project

/-- **The two-stage SSP tower**: nine full phase cells, reduced by the
orientation symmetry to three kernel trits, then by the magnitude observer to two
magnitudes, retaining `sign × depth-wheel phase`. -/
noncomputable def sspTower :
    SymmetryResolvedObserver FibreOrientation FullPhaseCell Bool (Bool × DepthWheelPhase) 9 :=
  towerOf ssp369Observer magnitudeExtension

/-- The three welded conclusions for the two-stage tower, plus the fact that its
certificate is literally the certificate of the one-stage observer. -/
theorem sspTower_theorem :
    (Function.Surjective sspTower.reduction.proj ∧
        ∀ g x, sspTower.reduction.proj (sspTower.reduction.actRich g x)
          = sspTower.reduction.actCoarse g (sspTower.reduction.proj x)) ∧
      (∀ x, sspTower.reopen (sspTower.reduction.proj x) (sspTower.residual x) = x) ∧
      Function.Injective (fun x => (sspTower.reduction.proj x, sspTower.residual x)) ∧
      (∀ x, 0 < sspTower.nondegeneracy x) ∧
      (∀ g x, sspTower.nondegeneracy (sspTower.reduction.actRich g x)
        = sspTower.nondegeneracy x) ∧
      (∀ x, sspTower.nondegeneracy x = ssp369Observer.nondegeneracy x) :=
  tower_theorem ssp369Observer magnitudeExtension

/-- The arithmetic of the tower: `9` rich states, `3` at the middle level, `2`
visible at the bottom, and a retained residual of size `6`.  The rich carrier
embeds into `visible × residual` (`2 × 6 = 12 ≥ 9`), which is what makes the
two-stage descent lossless. -/
theorem sspTower_cards :
    Fintype.card FullPhaseCell = 9 ∧ Fintype.card KernelTrit = 3 ∧
      Fintype.card Bool = 2 ∧ Fintype.card (Bool × DepthWheelPhase) = 6 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The second stage is a genuine further reduction, not a relabelling: it is
strictly non-injective, and its upstairs action is nontrivial while the induced
downstairs action is trivial. -/
theorem magnitudeStep_proper :
    ¬ Function.Injective magnitudeStep.proj ∧
      (∃ t, magnitudeStep.actRich .inverse t ≠ t) ∧
      (∀ g b, magnitudeStep.actCoarse g b = b) := by
  refine ⟨fun h => ?_, ⟨.negativeTrit, by decide⟩, fun _ _ => rfl⟩
  have : (KernelTrit.negativeTrit) = KernelTrit.positiveTrit := h (by decide)
  exact absurd this (by decide)

/-- The tower's residual is strictly bigger than the one-stage residual: the
extra Boolean is exactly the sign that the magnitude observer stops showing. -/
theorem sspTower_residual_grows :
    Fintype.card DepthWheelPhase < Fintype.card (Bool × DepthWheelPhase) := by decide

end Integration.ObserverTower
