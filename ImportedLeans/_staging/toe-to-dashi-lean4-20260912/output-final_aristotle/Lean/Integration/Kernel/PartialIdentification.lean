import Integration.Kernel.Quotient

/-!
# Partial identification: what to return when point descent fails

`Agda/DASHI/Cognition/PNF/SensibLawLegalOutcomeIdentifiabilityBidiExact.agda`
(in the 6 September tranche archive shipped with this project) carries a real
proof: `outcomeDegeneracyRefutesGlobalIdentifiability` derives `⊥` from a
degeneracy witness (two latent states with the same observed disposition and
different explanations) together with global identifiability.  It then keeps a
*fibre* of compatible explanation candidates, and distinguishes two consumer
goals — "list the compatible explanations", which can close, and "identify the
exact one", which stays open.  That second half is a `Bool` field
(`exactReasonResolved`) read by a `goalStatus` function on one fixture, and the
boundary declarations at the end are empty-type `→ ⊥` refutations.

The kernel already owns the negative half of this: a collision refutes descent
(`Integration.Kernel.Quotient.not_descendsThrough_of_collision`).  What it did
not own is the **positive** half — the object to return when point descent
fails.  This file supplies it: the compatible fibre, its soundness, the exact
characterisation of point identification as a singleton fibre, and the theorem
that the set-valued answer descends through the observation while the
point-valued one does not.

## What is proved

* `compatible o := {x | obs x = o}`, `compatible_eq_fibre` — the compatible set
  *is* the kernel's quotient class, so nothing new is being invented.
* **`truth_is_never_excluded`** (`mem_compatible_self`) and
  `compatible_nonempty` — the fibre is sound: the actual latent state is always
  in the returned set, so partial identification loses no truth.
* **`pointIdentified_iff_compatible_singleton`** — point identification of an
  observed value is exactly the compatible fibre being `{x}`.
* **`not_pointIdentified_of_collision`** — the Lean form of the Agda
  degeneracy theorem: two latent states with the same observation and different
  explanations refute point identification.  `explanation_does_not_descend`
  states the same fact as a non-descent.
* **`fibre_answer_descends`** — the positive result: the *set-valued* answer is
  a function of the observation alone, always, with no hypotheses.
* **`fibre_closes_while_point_stays_open`** — the two together on one model:
  the "list all compatible explanations" consumer descends and the "identify
  the exact state" consumer does not.  This is the consumer-relative reading of
  a failed descent.
* Reopening: `compatible_pair_subset`, `compatible_pair_ssubset` and
  **`reopening_gives_point_identification`** — an extra coordinate narrows the
  fibre, and a coordinate that separates the fibre completely restores point
  identification (via `Integration.Kernel.Quotient.Reopening`).

**Claim boundary.**  `Latent` and `Observation` are arbitrary types and `obs` an
arbitrary function.  Nothing is claimed about any inverse problem, legal
disposition or statistical model.
-/

namespace Integration.Kernel.PartialIdentification

open Integration.Kernel.Quotient Set

universe u v w

variable {Latent : Type u} {Observation : Type v} {Explanation : Type w}

/-! ## §1 The compatible fibre -/

variable (obs : Latent → Observation)

/-- Every latent state compatible with an observed value. -/
def compatible (o : Observation) : Set Latent := {x | obs x = o}

/-- The compatible set is the consumer quotient class of the observation map:
this is the same object the kernel already reasons about. -/
theorem compatible_eq_fibre (x : Latent) : compatible obs (obs x) = fibre obs x := rfl

variable {obs}

@[simp] theorem mem_compatible {o : Observation} {x : Latent} :
    x ∈ compatible obs o ↔ obs x = o := Iff.rfl

/-- **Partial identification is sound**: the actual state is never excluded from
the answer. -/
theorem truth_is_never_excluded (x : Latent) : x ∈ compatible obs (obs x) := rfl

theorem compatible_nonempty (x : Latent) : (compatible obs (obs x)).Nonempty :=
  ⟨x, truth_is_never_excluded x⟩

/-! ## §2 Point identification is a singleton fibre -/

/-- The observed value pins down exactly one latent state. -/
def PointIdentified (obs : Latent → Observation) (o : Observation) : Prop :=
  ∃! x : Latent, obs x = o

/-- **Point identification is exactly a singleton compatible fibre.** -/
theorem pointIdentified_iff_compatible_singleton {o : Observation} :
    PointIdentified obs o ↔ ∃ x, compatible obs o = {x} := by
  constructor
  · rintro ⟨x, hx, huniq⟩
    refine ⟨x, ?_⟩
    ext y
    exact ⟨fun hy => huniq y hy, fun hy => by rw [show y = x from hy]; exact hx⟩
  · rintro ⟨x, hx⟩
    have hxx : x ∈ compatible obs o := by rw [hx]; rfl
    exact ⟨x, hxx, fun y hy => by
      have : y ∈ compatible obs o := hy
      rw [hx] at this
      exact this⟩

/-- **A degeneracy witness refutes point identification.**  This is the Lean
form of `outcomeDegeneracyRefutesGlobalIdentifiability`. -/
theorem not_pointIdentified_of_collision {x y : Latent} (hobs : obs x = obs y) (hxy : x ≠ y) :
    ¬ PointIdentified obs (obs x) := by
  rintro ⟨z, -, huniq⟩
  exact hxy ((huniq x rfl).trans (huniq y hobs.symm).symm)

/-- The same fact as a non-descent: a latent coordinate the observation cannot
separate does not descend through the observation. -/
theorem explanation_does_not_descend {explanation : Latent → Explanation} {x y : Latent}
    (hobs : obs x = obs y) (hexp : explanation x ≠ explanation y) :
    ¬ DescendsThrough explanation obs :=
  not_descendsThrough_of_collision hobs hexp

/-! ## §3 The positive answer: the fibre always descends -/

/-- **The set-valued answer is always available.**  Whatever the observation map
does, "the set of latent states compatible with what was observed" is a function
of the observation alone — no hypotheses, no identification assumption. -/
theorem fibre_answer_descends (obs : Latent → Observation) :
    DescendsThrough (fun x => compatible obs (obs x)) obs :=
  ⟨compatible obs, fun _ => rfl⟩

/-- Nor does the fibre answer lose anything the observation had: it refines back
to the observation exactly on nonempty fibres. -/
theorem compatible_injOn_range {o o' : Observation} (x : Latent) (hx : obs x = o)
    (h : compatible obs o = compatible obs o') : o = o' := by
  have : x ∈ compatible obs o' := by rw [← h]; exact hx
  exact hx.symm.trans this

/-- A two-state model whose observation collapses both states. -/
def collapsedObs : Bool → Unit := fun _ => ()

/-- **When point descent fails, the fibre answer still closes.**  On the same
model: the compatible-set consumer descends through the observation, and the
identify-the-state consumer does not. -/
theorem fibre_closes_while_point_stays_open :
    DescendsThrough (fun b => compatible collapsedObs (collapsedObs b)) collapsedObs ∧
      ¬ DescendsThrough (id : Bool → Bool) collapsedObs := by
  refine ⟨fibre_answer_descends collapsedObs, ?_⟩
  exact not_descendsThrough_of_collision (x := true) (y := false) rfl (by decide)

/-! ## §4 Reopening towards a singleton -/

variable {Fine : Type w}

/-- Adding a coordinate narrows the compatible set. -/
theorem compatible_pair_subset (obs : Latent → Observation) (E : Latent → Fine) (x : Latent) :
    compatible (pair obs E) (pair obs E x) ⊆ compatible obs (obs x) :=
  fun _ h => congrArg Prod.fst h

/-- And strictly, when the new coordinate separates something the old one did
not. -/
theorem compatible_pair_ssubset {obs : Latent → Observation} {E : Latent → Fine} {x y : Latent}
    (hobs : obs y = obs x) (hE : E y ≠ E x) :
    compatible (pair obs E) (pair obs E x) ⊂ compatible obs (obs x) :=
  fibre_pair_ssubset hobs hE

/-- **Reopening restores point identification.**  If a retained fine coordinate
separates the state completely — an `Integration.Kernel.Quotient.Reopening` —
then every compatible fibre of the pair observer is a singleton, so the
previously partially identified question is now point identified. -/
theorem reopening_gives_point_identification (R : Reopening Latent Observation Fine)
    (x : Latent) : PointIdentified (pair R.coarse R.relativeFine) (pair R.coarse R.relativeFine x) :=
  pointIdentified_iff_compatible_singleton.mpr ⟨x, R.fibre_pair_eq_singleton x⟩

/-- The converse direction is the honest limitation: a fine coordinate that does
not separate leaves the fibre non-singleton, so reopening has to be *earned* by
an actually separating producer. -/
theorem no_point_identification_without_separation {obs : Latent → Observation}
    {E : Latent → Fine} {x y : Latent} (hobs : obs x = obs y) (hE : E x = E y) (hxy : x ≠ y) :
    ¬ PointIdentified (pair obs E) (pair obs E x) :=
  not_pointIdentified_of_collision (Prod.ext hobs hE) hxy

end Integration.Kernel.PartialIdentification
