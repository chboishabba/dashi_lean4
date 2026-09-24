/-
# Equal cardinality is not a map

The structural discipline the spine enforces: two carriers of the same size are
never thereby identified.  This file makes that a theorem rather than a slogan.

* `Spine.exists_two_distinct_equivs` — as soon as a carrier has at least two
  elements, an equinumerous pair admits at least two *different* bijections, so
  "the" bijection does not exist: a claimed identification must name a specific
  map.
* `Spine.no_structure_preserving_equiv_of_orbit_obstruction` — the useful form:
  if a group-like self-map is fixed-point-free on one side but every candidate
  transported map must fix a point on the other, no equivariant identification
  exists.  This is the abstract shape of the concrete refutation
  `Spine.Ogg.no_equivariant_labelling` (the internal `5 × 3` carrier versus the
  fifteen supersingular primes).
* `Spine.card_eq_of_equiv` records the trivial converse direction: a map gives
  equal cardinality, never the other way round.
-/
import Mathlib
import Spine.OggGrid

namespace Spine

/-- Equal cardinality yields *some* bijection, but never a canonical one: with at
least two elements there are always at least two distinct bijections. -/
theorem exists_two_distinct_equivs {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (hcard : Fintype.card α = Fintype.card β) (h2 : 2 ≤ Fintype.card α) :
    ∃ e f : α ≃ β, e ≠ f := by
  classical
  obtain ⟨e⟩ := Fintype.card_eq.mp hcard
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := α) (by omega)
  refine ⟨e, (Equiv.swap a b).trans e, ?_⟩
  intro h
  have := congrArg (fun g : α ≃ β => g a) h
  simp only [Equiv.trans_apply, Equiv.swap_apply_left] at this
  exact hab (e.injective this)

/-- A bijection gives equal cardinality.  (The implication only runs this way.) -/
theorem card_eq_of_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card α = Fintype.card β := Fintype.card_congr e

/-- **The transport obstruction, abstractly.**  If `s` is a fixed-point-free
self-map of `α` and every self-map of `β` in the class `P` has a fixed point,
then no bijection `α ≃ β` carries `s` into the class `P`. -/
theorem no_structure_preserving_equiv_of_orbit_obstruction
    {α β : Type*} (s : α → α) (P : (β → β) → Prop)
    (hs : ∀ x, s x ≠ x)
    (hP : ∀ t : β → β, P t → ∃ y, t y = y) :
    ¬ ∃ e : α ≃ β, P (fun y => e (s (e.symm y))) := by
  rintro ⟨e, hPe⟩
  obtain ⟨y, hy⟩ := hP _ hPe
  have : s (e.symm y) = e.symm y := by
    have := congrArg e.symm hy
    simpa using this
  exact hs _ this

end Spine
