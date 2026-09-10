import Integration.Kernel.Probe

/-!
# The assay AND node as an instance of the probe layer

The chemistry lane's assay problem is an AND node with eight leaves:
availability/use relevance, regulatory route, laboratory scope, matrix and
extraction behaviour, signal mechanism, LOD/LOQ, decision rule, and safety
relevance.  This file instantiates `Integration.Kernel.Probe` on it — no new
search machinery, exactly the point of the consolidation.

The possibility space is `Ω = Bool × Bool`: whether the analyte is above the
decision limit, and whether the matrix interferes.  The consumer coordinate is
the compliance decision, which depends on the first coordinate only.

* `assay_narrows_but_does_not_resolve` — the six leaves that *do* have targets
  (documentary and procedural ones) strictly narrow the residual fibre and
  leave the compliance collision open, because the two empirical leaves —
  matrix/extraction behaviour and LOD/LOQ — are unknown and therefore recorded
  with **no targets**.
* `assay_vacuously_succeeds` — under the "an action with no targets is a
  successful terminal" convention the node with only those two leaves reports
  success while changing nothing: the instance of
  `Probe.vacuous_success_is_not_resolution`.
* `new_measurement_separates` — an actual additional measurement, i.e. a channel
  whose read-out determines the compliance coordinate, resolves the collision
  whatever it returns.
* `reinterpretation_does_not_separate` — re-reading the existing result, modelled
  as a channel constant on the current fibre, leaves the collision exactly where
  it was.

**Claim boundary.** No chemistry is formalised: "above the decision limit" is a
Boolean coordinate and a "measurement" is a function on a four-element space.
The content is the search semantics, not the assay.
-/

namespace Integration.Kernel.Instances.Assay

open Set Integration.Kernel.ResidualFibre Integration.Kernel.Probe

/-- A world: `(above the decision limit, matrix interferes)`. -/
abbrev World := Bool × Bool

/-- The compliance decision the consumer needs. -/
def compliant (w : World) : Bool := !w.1

/-- The eight leaves of the assay AND node. -/
inductive AssayLeaf
  /-- Is the substance in use here at all? -/
  | availability
  /-- Which regulatory route applies? -/
  | regulatory
  /-- What is the laboratory's accredited scope? -/
  | labScope
  /-- How does the matrix behave under extraction? *(unknown here)* -/
  | matrixBehaviour
  /-- What is the signal mechanism? -/
  | signalMechanism
  /-- What are the LOD and LOQ? *(unknown here)* -/
  | lodLoq
  /-- What is the decision rule? -/
  | decisionRule
  /-- What is the safety relevance? -/
  | safety
  deriving DecidableEq, Repr

/-- The documentary leaves constrain the matrix coordinate; the two empirical
leaves are unknown, so they carry no targets at all. -/
def targetsOf : AssayLeaf → List (Set World)
  | .matrixBehaviour => []
  | .lodLoq => []
  | _ => [{w | w.2 = false}]

/-- The node built from the six leaves that do have targets. -/
def documentedNode : AndNode World :=
  ⟨[⟨targetsOf .availability⟩, ⟨targetsOf .regulatory⟩, ⟨targetsOf .labScope⟩,
    ⟨targetsOf .signalMechanism⟩, ⟨targetsOf .decisionRule⟩, ⟨targetsOf .safety⟩]⟩

/-- The node built from the two unknown empirical leaves. -/
def empiricalNode : AndNode World :=
  ⟨[⟨targetsOf .matrixBehaviour⟩, ⟨targetsOf .lodLoq⟩]⟩

theorem documented_contribution :
    documentedNode.contribution univ = {w : World | w.2 = false} := by
  ext w
  simp [documentedNode, AndNode.contribution, targetsOf, refineAll, refineBy]

/-- **The documented leaves narrow the fibre and still leave the decision
open.** -/
theorem assay_narrows_but_does_not_resolve :
    documentedNode.contribution univ ⊂ univ ∧
      Collision (documentedNode.contribution univ) compliant := by
  constructor
  · refine ⟨subset_univ _, fun h => ?_⟩
    have : ((true, true) : World) ∈ documentedNode.contribution univ := h (mem_univ _)
    rw [documented_contribution] at this
    exact Bool.noConfusion this
  · rw [documented_contribution]
    exact ⟨(true, false), rfl, (false, false), rfl, by simp [compliant]⟩

/-- **An unknown empirical leaf is not an empty target list.**  The empirical
node satisfies the vacuous-success convention and contributes nothing. -/
theorem assay_vacuously_succeeds :
    empiricalNode.vacuouslySucceeds ∧
      empiricalNode.contribution (documentedNode.contribution univ)
        = documentedNode.contribution univ := by
  have hv : empiricalNode.vacuouslySucceeds := by
    intro l hl
    simp only [empiricalNode, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  exact ⟨hv, AndNode.contribution_eq_of_vacuous hv _⟩

/-- The collision is still there after the vacuously successful node. -/
theorem assay_collision_survives_vacuous_success :
    Collision (empiricalNode.contribution (documentedNode.contribution univ)) compliant := by
  rw [(assay_vacuously_succeeds).2]
  exact assay_narrows_but_does_not_resolve.2

/-- An additional measurement of the analyte coordinate. -/
def analyteChannel : Channel World Bool := ⟨Prod.fst⟩

/-- A re-reading of the existing documentary result: it reports the same thing
at every surviving world. -/
def reinterpretationChannel : Channel World Bool := ⟨Prod.snd⟩

/-- **Actual additional measurement separates the compliance collision.** -/
theorem new_measurement_separates (F : Set World) :
    ResolvesFor analyteChannel F compliant :=
  resolves_of_factors (g := fun b => !b) fun _ => rfl

/-- **Merely reinterpreting the existing result does not.**  On the documented
fibre the re-reading is constant, so the collision persists. -/
theorem reinterpretation_does_not_separate :
    Collision (refine (documentedNode.contribution univ) reinterpretationChannel false)
      compliant := by
  refine collision_persists_of_constant (O := reinterpretationChannel) ?_
    assay_narrows_but_does_not_resolve.2
  intro w hw
  rw [documented_contribution] at hw
  exact hw

end Integration.Kernel.Instances.Assay
