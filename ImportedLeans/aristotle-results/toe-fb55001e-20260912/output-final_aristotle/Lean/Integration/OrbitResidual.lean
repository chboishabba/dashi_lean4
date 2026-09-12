import Integration.ResidualQuotient

/-!
# What a symmetry quotient has to hide: the orbit–stabilizer residual bound

`Integration.ResidualQuotient` says that a projection which retains a residual is
lossless, and that the residual cannot be trivial once the coarse layer is
strictly smaller (`residual_not_subsingleton`).  Those are cardinality facts
about an arbitrary projection.  When the projection is the **orbit map** of a
group action, the size of what must be hidden is not arbitrary: it is determined
by the geometry of the orbits.

* `residual_injOn_fibre` — exact reopening forces the residual to be injective on
  every fibre of the projection.  This is the general principle of which the
  earlier cardinality bounds are consequences.
* `residual_orbit_injective` — for the orbit projection of a group action, the
  residual is therefore injective on each orbit.
* `card_orbit_le_card_residual` — hence the residual carrier is at least as large
  as every orbit.
* `index_stabilizer_le_card_residual` — **the orbit–stabilizer form**: since an
  orbit is in bijection with the coset space of the stabilizer, the residual must
  have at least `[G : Stab x]` elements.  So the amount of information a symmetry
  quotient has to hide is bounded below by the index of the point stabilizer,
  and for a free action by the order of the group (`card_group_le_card_residual`).
* `cosetResidual`, `cosetResidual_injective` — more than a bound: the coset space
  `G ⧸ Stab x` embeds canonically into the residual carrier, so the hidden
  information literally records which coset of the stabilizer was used.

The statements use Mathlib's `MulAction`, `orbit` and `stabilizer`, so they apply
to any group action, finite or not, with the finiteness needed only where a
cardinality is compared.
-/

namespace Integration.OrbitResidual

open Integration.Residual
open MulAction

variable {Rich Coarse Res : Type}

/-- **Exact reopening separates each fibre.**  If two states have the same coarse
observation, their residuals differ unless the states are equal: the residual
does the whole job of distinguishing points inside a fibre. -/
theorem residual_injOn_fibre (q : ResidualQuotient Rich Coarse Res) {x y : Rich}
    (hproj : q.project x = q.project y) (hres : q.residual x = q.residual y) : x = y := by
  refine injective_pair q ?_
  show (q.project x, q.residual x) = (q.project y, q.residual y)
  rw [hproj, hres]

variable {G X : Type} [Group G] [MulAction G X]

/-- The orbit projection of a group action. -/
def orbitProj (G X : Type) [Group G] [MulAction G X] : X → Quotient (orbitRel G X) :=
  Quotient.mk (orbitRel G X)

theorem orbitProj_eq_iff {x y : X} : orbitProj G X x = orbitProj G X y ↔ ∃ g : G, g • y = x :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

variable (q : ResidualQuotient X (Quotient (orbitRel G X)) Res)

/-- **The residual separates each orbit.**  A residual that reopens the orbit
quotient is injective on every orbit. -/
theorem residual_orbit_injective (hq : q.project = orbitProj G X) (x : X) :
    Function.Injective (fun y : orbit G x => q.residual (y : X)) := by
  rintro ⟨y, hy⟩ ⟨z, hz⟩ h
  obtain ⟨gy, rfl⟩ := hy
  obtain ⟨gz, rfl⟩ := hz
  have hproj : q.project (gy • x) = q.project (gz • x) := by
    rw [hq]
    exact orbitProj_eq_iff.mpr ⟨gy * gz⁻¹, by rw [mul_smul, inv_smul_smul]⟩
  exact Subtype.ext (residual_injOn_fibre q hproj h)

/-- **Every orbit fits inside the residual.** -/
theorem card_orbit_le_card_residual [Finite Res] (hq : q.project = orbitProj G X) (x : X) :
    Nat.card (orbit G x) ≤ Nat.card Res :=
  Nat.card_le_card_of_injective _ (residual_orbit_injective q hq x)

/-- **The orbit–stabilizer residual bound.**  The residual of a symmetry quotient
must carry at least `[G : Stab x]` states: the hidden information is bounded
below by the index of the point stabilizer. -/
theorem index_stabilizer_le_card_residual [Finite Res] (hq : q.project = orbitProj G X) (x : X) :
    (stabilizer G x).index ≤ Nat.card Res := by
  have hcard : Nat.card (orbit G x) = (stabilizer G x).index :=
    Nat.card_congr (orbitEquivQuotientStabilizer G x)
  rw [← hcard]
  exact card_orbit_le_card_residual q hq x

/-- **The canonical coset reading of the residual.**  Transporting a coset of the
stabilizer to the corresponding point of the orbit and reading its residual gives
a map `G ⧸ Stab x → Res` built from the action alone. -/
noncomputable def cosetResidual (x : X) : G ⧸ stabilizer G x → Res :=
  fun c => q.residual ((orbitEquivQuotientStabilizer G x).symm c : X)

/-- **The residual contains a canonical copy of `G ⧸ Stab x`.**  The coset
reading is injective, so the symmetry-theoretic content `G ⧸ Stab x` embeds in
the residual carrier: the hidden information is not merely large enough, it
literally records the coset. -/
theorem cosetResidual_injective (hq : q.project = orbitProj G X) (x : X) :
    Function.Injective (cosetResidual q x) :=
  (residual_orbit_injective q hq x).comp (orbitEquivQuotientStabilizer G x).symm.injective

/-- The coset reading recovers the residual of every point of the orbit. -/
theorem cosetResidual_apply (x : X) (g : G) :
    cosetResidual q x (QuotientGroup.mk g) = q.residual (g • x) := rfl

/-- For a free action the bound is the order of the whole symmetry group. -/
theorem card_group_le_card_residual [Finite Res] (hq : q.project = orbitProj G X)
    (x : X) (hfree : stabilizer G x = ⊥) : Nat.card G ≤ Nat.card Res := by
  have h := index_stabilizer_le_card_residual q hq x
  rwa [hfree, Subgroup.index_bot] at h

end Integration.OrbitResidual
