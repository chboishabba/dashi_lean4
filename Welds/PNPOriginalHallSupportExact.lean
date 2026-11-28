import Welds.PNPOriginalPartitionCapacityExact

namespace PNPOriginalHallSupport

-- The old global pigeonhole theorem is instantiated on an actual
-- subset of rows and its actual finite neighbour columns.
theorem hall_defect {V R C : Type*} [Fintype R] [Fintype C]
    (row : V → R) (col : V → C) (selected : V → Prop)
    (X : Finset R) (Y : Finset C)
    (hrow : ∀ r∈X, ∃ v, selected v ∧ row v=r)
    (neighbour : ∀ v, selected v → row v∈X → col v∈Y)
    (hcol : ∀ u v, selected u → selected v → col u=col v → u=v)
    (excess : Y.card<X.card) : False := by
  classical
  let T := {v : V // selected v ∧ row v∈X}
  let row' : T → {r // r∈X} := fun v => ⟨row v.val,v.property.2⟩
  let col' : T → {c // c∈Y} := fun v =>
    ⟨col v.val,neighbour v.val v.property.1 v.property.2⟩
  have cover : ∀ r : {r // r∈X}, ∃ v : T, True ∧ row' v=r := by
    intro r
    obtain ⟨v,hv,hr⟩ := hrow r.val r.property
    exact ⟨⟨v,hv,by rw [hr]; exact r.property⟩,trivial,Subtype.ext hr⟩
  have capacity : ∀ u v : T, True → True → col' u=col' v → u=v := by
    intro u v _ _ e
    apply Subtype.ext
    exact hcol u.val v.val u.property.1 v.property.1 (congrArg Subtype.val e)
  have h := PNPOriginalPartitionCapacity.partition_capacity row' col'
    (fun _ => True) cover capacity
  simpa using (Nat.not_lt_of_ge (by simpa using h : X.card≤Y.card) excess)

-- Force an original selected variable a. Every other required row
-- is disjoint from its row; every other selected variable must avoid
-- a's column. A Hall defect in that conditional source rules out a,
-- even when the unconditioned projected matching is feasible.
theorem forced_edge_absent {V R C : Type*} [Fintype R] [Fintype C]
    (row : V → R) (col : V → C) (selected : V → Prop)
    (a : V) (X : Finset R) (Y : Finset C)
    (hrow : ∀ r∈X, ∃ v, selected v ∧ row v=r)
    (noRow : row a∉X) (noCol : col a∉Y)
    (neighbour : ∀ v, selected v → row v∈X →
      col v∈Y ∨ col v=col a)
    (hcol : ∀ u v, selected u → selected v → col u=col v → u=v)
    (excess : Y.card<X.card) : ¬ selected a := by
  intro ha
  apply hall_defect row col selected X Y hrow _ hcol excess
  intro v hv hr
  rcases neighbour v hv hr with h|h
  · exact h
  · have e := hcol v a hv ha h
    subst v
    exact False.elim (noRow hr)

-- Adding the negative unit for each independently justified absent
-- edge preserves the original satisfying set in BOTH directions.
theorem retire_sound {V : Type*} (F : (V → Prop) → Prop)
    (removed : V → Prop)
    (justified : ∀ x, F x → ∀ v, removed v → ¬ x v) :
    ∀ x, F x ↔ F x ∧ (∀ v, removed v → ¬ x v) := by
  intro x
  exact ⟨fun hx => ⟨hx,justified x hx⟩,And.left⟩

-- In actual tripartite exact cover, each pair of partitions satisfies
-- these row and column hypotheses; missing pair support is therefore
-- a sound negative pin, not a claim that pair support is sufficient.
end PNPOriginalHallSupport
