import Integration.Kernel.DeclaredRealised
import Integration.Kernel.Reopen

/-!
# Weld: operational realisation → remedy and runtime feedback, on one abstraction

`Integration.Kernel.DeclaredRealised` proves that declaration, acknowledgement
and realisation are three different coordinates and that the success test
belongs to the consumer.  `Integration.Kernel.Reopen` proves that a revision
reopens exactly the certificates whose history meets it.  Nothing yet made the
two meet, and the concrete question the corpus keeps asking is precisely the
join of them: *when only one consumer's outcome test fails, what has to be done
again?*

This file answers that with both consumers reading the **same** realised
episode.

## What is proved

* `Consumer`, `criterion` — two consumers over one `DeclaredRealised.Episode`:
  a runtime monitor that accepts an acknowledged execution, and a remedy
  consumer that accepts only an observed outcome.
* **`consumers_disagree_on_one_episode`** — they really are different tests of
  the same object; `verdict_does_not_descend_through_episode` restates this as
  a non-descent, so no reading of the world alone answers "did it close?".
* `revision`, `reopenedAfter` — the feedback rule: the failing consumers'
  edges are revised, and the certificates that used them reopen.
* **`only_failing_consumer_reopens`** — the selectivity theorem in this
  instance: a certificate whose history avoids the failing consumer's edge
  stays closed even though the episode as a whole did not fully succeed.
* **`full_success_reopens_nothing`** — and if no consumer fails, nothing is
  reopened at all, so the feedback loop is quiescent on success.
* `runtime_success_does_not_close_the_remedy` — the substantive consequence for
  the two-sided deployment: the acknowledged-but-unrealised episode passes the
  runtime consumer, fails the remedy consumer, and reopens exactly the remedy
  certificate.

**Claim boundary.**  Episodes are the four Booleans of
`Integration.Kernel.DeclaredRealised`; consumers, certificates and edges are
finite labels stipulated here.  Nothing models an actual court, order,
regulator, deployment or execution engine.
-/

namespace Integration.Kernel.Welds.RemedyRuntimeFeedback

open Integration.Kernel.Quotient Integration.Kernel.DeclaredRealised
open Integration.Kernel.Reopen

/-! ## §1 Two consumers of one realised episode -/

/-- The two consumers of the same episode. -/
inductive Consumer : Type
  /-- The execution monitor: an acknowledged step counts as done. -/
  | runtime
  /-- The affected party: only an observed outcome counts. -/
  | remedy
  deriving DecidableEq, Repr

open Consumer

/-- Each consumer's outcome test, applied to the shared episode. -/
def criterion : Consumer → Episode → Bool
  | runtime => Episode.acknowledged
  | remedy => Episode.realised

/-- The verdict of a consumer on an episode. -/
def verdict (c : Consumer) (e : Episode) : Bool := criterion c e

/-- **One episode, two verdicts.**  The acknowledged-but-unrealised episode
passes the runtime consumer and fails the remedy consumer. -/
theorem consumers_disagree_on_one_episode :
    verdict runtime acknowledgedNotRealised = true ∧
      verdict remedy acknowledgedNotRealised = false := ⟨rfl, rfl⟩

/-- Stated as a non-descent: the episode alone does not carry the verdict. -/
theorem verdict_does_not_descend_through_episode :
    ¬ DescendsThrough (fun p : Consumer × Episode => verdict p.1 p.2)
        (fun p : Consumer × Episode => p.2) :=
  not_descendsThrough_of_collision
    (x := (runtime, acknowledgedNotRealised)) (y := (remedy, acknowledgedNotRealised))
    rfl (by decide)

/-- The (consumer, episode) pair is the right index, exactly as in
`DeclaredRealised.success_descends_through_pair`. -/
theorem verdict_descends_through_pair :
    DescendsThrough (fun p : Consumer × Episode => verdict p.1 p.2) id :=
  ⟨fun p => verdict p.1 p.2, fun _ => rfl⟩

/-! ## §2 Certificates, and what a failure reopens -/

/-- The certificates maintained over this deployment. -/
inductive Cert : Type
  /-- A certificate that only used the runtime consumer's outcome. -/
  | runtimeOnly
  /-- A certificate that only used the remedy consumer's outcome. -/
  | remedyOnly
  /-- A certificate that used both. -/
  | joint
  deriving DecidableEq, Repr

open Cert

/-- Which consumers' outcomes each certificate's derivation used.  The edges of
the dependency graph are the consumers themselves. -/
def deployment : DepGraph Cert Consumer where
  history
  | runtimeOnly => {runtime}
  | remedyOnly => {remedy}
  | joint => {runtime, remedy}

/-- The consumers whose outcome test the episode fails. -/
def failing (e : Episode) : Set Consumer := {c | verdict c e = false}

/-- The revision an episode triggers: exactly the failing consumers' edges. -/
def revision (e : Episode) : Set Consumer := failing e

/-- The certificates reopened by an episode. -/
def reopenedAfter (e : Episode) : Set Cert := reopened deployment (revision e)

/-- **Reopening is selective, driven by which consumer failed.**  A certificate
whose derivation avoided the failing consumer stays closed. -/
theorem only_failing_consumer_reopens {e : Episode} {c : Cert}
    (h : Disjoint (deployment.history c) (revision e)) : c ∉ reopenedAfter e :=
  stays_closed_of_disjoint h

/-- A certificate that used a failing consumer's outcome does reopen. -/
theorem reopens_of_failing_edge {e : Episode} {c : Cert} {k : Consumer}
    (hk : verdict k e = false) (hc : k ∈ deployment.history c) : c ∈ reopenedAfter e :=
  reopen_of_revised_edge hk hc

/-- **A fully realised episode reopens nothing.** -/
theorem full_success_reopens_nothing : reopenedAfter fullyRealised = ∅ := by
  have : revision fullyRealised = (∅ : Set Consumer) := by
    ext c; cases c <;> simp [revision, failing, verdict, criterion, fullyRealised]
  rw [reopenedAfter, this, reopened_empty]

/-- On the acknowledged-but-unrealised episode, exactly the remedy consumer
fails. -/
theorem revision_of_acknowledgedNotRealised :
    revision acknowledgedNotRealised = {remedy} := by
  ext c
  cases c <;>
    simp [revision, failing, verdict, criterion, acknowledgedNotRealised]

/-- **Runtime success does not close the remedy, and the reopening is exactly
the remedy side.**  The runtime-only certificate survives, the remedy-only and
joint certificates reopen. -/
theorem runtime_success_does_not_close_the_remedy :
    verdict runtime acknowledgedNotRealised = true ∧
      runtimeOnly ∉ reopenedAfter acknowledgedNotRealised ∧
        remedyOnly ∈ reopenedAfter acknowledgedNotRealised ∧
          joint ∈ reopenedAfter acknowledgedNotRealised := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rintro ⟨k, hk, hc⟩
    rw [revision_of_acknowledgedNotRealised] at hk
    cases hk
    exact Consumer.noConfusion hc
  · exact ⟨remedy, by rw [revision_of_acknowledgedNotRealised]; rfl, rfl⟩
  · exact ⟨remedy, by rw [revision_of_acknowledgedNotRealised]; rfl, Or.inr rfl⟩

/-- The remedy consumer's receipt is the one that closes the remedy: a receipt
for the target state in the sense of `DeclaredRealised.Receipt` forces the
remedy verdict. -/
theorem remedy_receipt_closes (r : Receipt true) : verdict remedy r.episode = true :=
  r.observed

/-- And the acknowledgement is not such a receipt. -/
theorem acknowledgement_is_not_a_remedy_receipt :
    verdict runtime acknowledgedNotRealised = true ∧
      verdict remedy acknowledgedNotRealised ≠ true := ⟨rfl, by decide⟩

end Integration.Kernel.Welds.RemedyRuntimeFeedback
