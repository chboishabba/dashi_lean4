import Integration.StructureMorphism

/-!
# Semantic reduction is not computational locality

A reduction that produces the same relation is not thereby a reduction that
produces it cheaply.  The two are different certificates and this file keeps
them apart, because the confusion has a physical analogue: a small retained or
coarse-grained state does not by itself imply cheap or local microscopic
dynamics.

The formalisation is deliberately minimal.  A **plan** is a finite list of
elementary steps; its **semantics** is their composite and its **exposure** is
the number of intermediate values it materialises.

Contents.

* `Plan`, `eval`, `exposure` — the language;
* `eval_append`, `exposure_append` — semantics composes, cost adds;
* `semantic_parity_not_bounded_exposure` — **the separation**: two plans with
  identical semantics and different exposure;
* `exposure_unbounded` — and worse: for every bound there is a plan with that
  semantics exceeding it.  So extensional identity of the projection places no
  bound at all on intermediate work;
* `LocalRealisation` — the optional extra certificate: a semantics together with
  a plan realising it within a stated exposure;
* `localRealisation_transfers` — the certificate does transfer along semantic
  equality (it is a property of the semantics *plus* a witness), while
  `no_localRealisation_from_semantics_alone` records that it cannot be
  manufactured from the semantics alone, because the semantics is compatible
  with unbounded exposure.

Nothing here is a complexity-theoretic lower bound; the content is the typed
distinction between the two certificates.
-/

namespace Integration.LocalRealisation

variable {X : Type*}

/-- A plan: a finite list of elementary steps, applied left to right. -/
abbrev Plan (X : Type*) : Type _ := List (X → X)

/-- The semantics of a plan. -/
def eval : Plan X → X → X
  | [], x => x
  | f :: fs, x => eval fs (f x)

/-- The exposure of a plan: how many intermediate values it materialises. -/
def exposure (p : Plan X) : ℕ := p.length

@[simp] theorem eval_nil (x : X) : eval ([] : Plan X) x = x := rfl

@[simp] theorem eval_cons (f : X → X) (fs : Plan X) (x : X) :
    eval (f :: fs) x = eval fs (f x) := rfl

theorem eval_append (p q : Plan X) (x : X) : eval (p ++ q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons f fs ih => simpa using ih (f x)

@[simp] theorem exposure_append (p q : Plan X) :
    exposure (p ++ q) = exposure p + exposure q := List.length_append

/-- The plan consisting of `n` copies of the identity step. -/
def idPlan (X : Type*) : ℕ → Plan X
  | 0 => []
  | n + 1 => id :: idPlan X n

@[simp] theorem eval_idPlan (n : ℕ) (x : X) : eval (idPlan X n) x = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa [idPlan] using ih x

@[simp] theorem exposure_idPlan (n : ℕ) : exposure (idPlan X n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [idPlan, exposure] using ih

/-- **Semantic parity does not bound exposure.**  Two plans with identical
semantics and different exposure. -/
theorem semantic_parity_not_bounded_exposure :
    ∃ p q : Plan ℕ, (∀ x, eval p x = eval q x) ∧ exposure p ≠ exposure q := by
  refine ⟨idPlan ℕ 0, idPlan ℕ 1, fun x => by simp, ?_⟩
  simp

/-- **And there is no bound at all.**  For every `N` there is a plan with the
same semantics and exposure greater than `N`. -/
theorem exposure_unbounded (N : ℕ) :
    ∃ p : Plan ℕ, (∀ x, eval p x = x) ∧ N < exposure p := by
  refine ⟨idPlan ℕ (N + 1), fun x => by simp, ?_⟩
  simp

/-- The optional extra certificate: this semantics is realised by a plan of at
most the stated exposure. -/
def HasLocalRealisation (f : X → X) (bound : ℕ) : Prop :=
  ∃ p : Plan X, (∀ x, eval p x = f x) ∧ exposure p ≤ bound

/-- The certificate is a property of the semantics: it transfers across
extensional equality. -/
theorem localRealisation_transfers {f g : X → X} (h : ∀ x, f x = g x) {b : ℕ}
    (hf : HasLocalRealisation f b) : HasLocalRealisation g b := by
  obtain ⟨p, hp, hb⟩ := hf
  exact ⟨p, fun x => (hp x).trans (h x), hb⟩

/-- But it is not *implied* by the semantics: the same semantics is compatible
with arbitrarily large exposure, so a bound must be certified separately. -/
theorem no_localRealisation_from_semantics_alone :
    ∀ N : ℕ, ∃ p : Plan ℕ, (∀ x, eval p x = id x) ∧ ¬ exposure p ≤ N := by
  intro N
  obtain ⟨p, hp, hlt⟩ := exposure_unbounded N
  exact ⟨p, hp, not_le.mpr hlt⟩

end Integration.LocalRealisation
