import Integration.CommutatorObservability

/-!
# The holonomy lane: an open socket, with the obligation made explicit

`Agda/DASHI/Biology/Levin/HolonomyReferenceFrameBoundary.agda` declares records
whose fields are free `Bool`s — `closedPath`, `transportedWithoutLocalRotation`,
`returnedWithPhaseDefect`, `observableActionChanged`, `orderOfOperationsMatters`
— and a boundary record whose only other field is a `String`.  It defines **no**
transport map and proves **no** loop holonomy.  It must therefore not be filed
as an instance of `Integration.CommutatorObservability`; it is an open socket.

This file does two things.

1. **Records the underdetermination.**  The flags are free: two inhabitants can
   agree on the path record and disagree on whether the observable action
   changed (`flags_underdetermined`), and the phase-defect flag can be set to
   `true` with no supporting structure whatsoever
   (`phaseDefect_flag_is_free`).

2. **States the obligation exactly**, in the vocabulary of the owner, and shows
   it is a real and non-trivial question: a loop transport `T : E → E` on a
   fibre, together with an observation; the obligation is to exhibit a genuine
   defect `T x ≠ x`, and then to say what the observer does with it.
   `observed_defect_implies_defect` is the easy direction, and
   `defect_can_be_invisible` is the content: a fibre with a defect at every
   point that the observation erases completely, while a finer observation
   recovers it.  So "there is a phase defect" and "the observer sees a phase
   defect" are different obligations, and the corpus discharges neither.

Nothing here asserts that any biological, physical or geometric system has
holonomy.  The carriers are `Bool` and `Bool × Bool`.
-/

namespace Integration.HolonomySocket

open Integration.CommutatorObservability

/-! ## The corpus records, and their freedom -/

/-- Mirror of the Agda `InternalTransportPath`. -/
structure InternalTransportPath where
  /-- Whether the path is declared closed. -/
  closedPath : Bool
  /-- Whether transport is declared free of local rotation. -/
  transportedWithoutLocalRotation : Bool
  /-- Whether the return is declared to carry a phase defect. -/
  returnedWithPhaseDefect : Bool
  deriving DecidableEq, Repr

/-- Mirror of the Agda `ReferenceFrameChangeWitness`. -/
structure ReferenceFrameChangeWitness where
  /-- The declared path. -/
  path : InternalTransportPath
  /-- Whether the observable action is declared to have changed. -/
  observableActionChanged : Bool
  /-- Whether order of operations is declared to matter. -/
  orderOfOperationsMatters : Bool
  deriving DecidableEq, Repr

/-- **The flags are free.**  Two witnesses agreeing on the whole path record
disagree on the observable action, so the path fields constrain the observable
one not at all. -/
theorem flags_underdetermined :
    ∃ w v : ReferenceFrameChangeWitness,
      w.path = v.path ∧ w.observableActionChanged ≠ v.observableActionChanged :=
  ⟨⟨⟨true, true, true⟩, true, true⟩, ⟨⟨true, true, true⟩, false, true⟩, rfl,
    Bool.false_ne_true.symm⟩

/-- **And the phase-defect flag is free.**  It can be set with no transport map,
no fibre and no loop anywhere in the record. -/
theorem phaseDefect_flag_is_free :
    ∃ p : InternalTransportPath, p.returnedWithPhaseDefect = true ∧
      ∃ q : InternalTransportPath, q.returnedWithPhaseDefect = false ∧
        p.closedPath = q.closedPath :=
  ⟨⟨true, true, true⟩, rfl, ⟨true, true, false⟩, rfl, rfl⟩

/-! ## The obligation, stated -/

/-- The data the corpus does **not** supply: a fibre, a transport around a fixed
closed path, and an observation of the fibre. -/
structure LoopHolonomy where
  /-- The fibre over the base point of the loop. -/
  Fibre : Type
  /-- What the observer reports. -/
  Obs : Type
  /-- Transport once around the closed path. -/
  transport : Fibre → Fibre
  /-- The observation. -/
  observe : Fibre → Obs

/-- **Obligation 1**: the transport around the loop is not the identity. -/
def HasPhaseDefect (H : LoopHolonomy) : Prop := ∃ x, H.transport x ≠ x

/-- **Obligation 2**: the observer can tell. -/
def ObserverSeesDefect (H : LoopHolonomy) : Prop :=
  ∃ x, H.observe (H.transport x) ≠ H.observe x

/-- The easy direction: an observed defect is a defect. -/
theorem observed_defect_implies_defect {H : LoopHolonomy} (h : ObserverSeesDefect H) :
    HasPhaseDefect H := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, fun heq => hx (by rw [heq])⟩

/-- A fibre carrying a phase and a marker; transport flips the phase. -/
def phaseFibre : LoopHolonomy where
  Fibre := Bool × Bool
  Obs := Bool
  transport := fun s => (!s.1, s.2)
  observe := fun s => s.2

/-- The same fibre and transport, observed completely. -/
def phaseFibreFine : LoopHolonomy where
  Fibre := Bool × Bool
  Obs := Bool × Bool
  transport := fun s => (!s.1, s.2)
  observe := id

/-- **The content of the socket.**  There is a genuine defect at every point of
the fibre, the marker observation erases it entirely, and the complete
observation recovers it.  So discharging obligation 1 does not discharge
obligation 2, and a `Bool` flag naming either of them supplies neither. -/
theorem defect_can_be_invisible :
    HasPhaseDefect phaseFibre ∧ ¬ ObserverSeesDefect phaseFibre ∧
      ObserverSeesDefect phaseFibreFine := by
  refine ⟨⟨(false, false), ?_⟩, ?_, ⟨(false, false), ?_⟩⟩
  · intro h
    exact absurd (congrArg Prod.fst h) (by decide)
  · rintro ⟨x, hx⟩
    exact hx rfl
  · intro h
    exact absurd (congrArg Prod.fst h) (by decide)

/-- The socket, restated against the owner it would fill.  The owner's pattern —
fine noncommutativity with coarse flatness — is realised on an explicit carrier
(`cubie_hidden_order`); what the corpus's holonomy module would have to supply,
and does not, is a transport and an observation of its own. -/
theorem owner_is_ready :
    (CoarseFlat obs tA tB ∧ FineNoncommutative tA tB) ∧
      HasPhaseDefect phaseFibre ∧ ¬ ObserverSeesDefect phaseFibre :=
  ⟨cubie_hidden_order, defect_can_be_invisible.1, defect_can_be_invisible.2.1⟩

end Integration.HolonomySocket
