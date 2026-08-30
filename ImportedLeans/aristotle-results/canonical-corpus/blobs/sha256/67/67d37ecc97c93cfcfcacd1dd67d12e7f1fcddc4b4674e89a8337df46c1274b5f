import Integration.TernaryHub
import Integration.EpistemicTrit
import Integration.DNAMarginTrit

/-!
# Closing the ternary hub: one theorem instead of eight hand-written rows

`Integration.TernaryHub` transports eight different three-element corpus
carriers — `Trit`, `TriTruth`, `Digit369`, `SSPTrit`, `TritCode`, `BTBranch`,
and (added in the sewing round) `Integration.Ontology.EpistemicTrit` and
`Integration.DNAMarginTrit.ChemistryMargin` — onto the balanced `ZMod 3`
coordinate, each by a hand-written equivalence.

This file proves the general statement those eight instantiate, so any *future*
three-element carrier is an automatic instance rather than another hand-written
row.

## The statement

`ternaryHub_of_involution`: let `A` be a type with exactly three elements
carrying a self-inverse map `σ` whose **only** fixed point is a distinguished
`z`.  Then `A` with `σ` is `ZMod 3` with negation: there is a
`Integration.Levels.Transport A (ZMod 3) σ zneg` sending `z` to `0`.

All four hypotheses are checkable by `decide` for a concrete finite carrier, so
using the theorem costs four `by decide`s.  `six_carriers_from_closure` collects
six worked instantiations.

`ternaryHub_not_unique` is the honest complement: such a coordinate is **not**
unique — it is determined only up to an overall sign, because negating a
balanced coordinate gives another one.  `ternaryHub_two_coordinates` exhibits
the two explicitly, so the non-uniqueness is a first-class negative rather than
an omission.

## Claim boundary

`A` is a three-element label type and `σ` is a map on it.  Nothing is asserted
about evidence, chemistry, biology or physics; the theorem is a statement about
involutions on three-element sets.
-/

namespace Integration.TernaryHubClosure

open Integration.Levels
open Integration.TernaryHub

variable {A : Type} [DecidableEq A] [Fintype A]

/-- A three-element carrier with a self-inverse map whose only fixed point is
`z`.  All four fields are `decide`-able for a concrete finite `A`. -/
structure BalancedInvolution (A : Type) [Fintype A] (σ : A → A) (z : A) : Prop where
  /-- The carrier has exactly three elements. -/
  card : Fintype.card A = 3
  /-- `σ` is self-inverse. -/
  involutive : ∀ a, σ (σ a) = a
  /-- `z` is fixed. -/
  fixes : σ z = z
  /-- ...and it is the only fixed point. -/
  onlyFixed : ∀ a, σ a = a → a = z

variable {σ : A → A} {z : A}

/-- The two non-fixed points, extracted. -/
private theorem two_others (h : BalancedInvolution A σ z) :
    ∃ a b : A, a ≠ b ∧ a ≠ z ∧ b ≠ z ∧ σ a = b ∧ σ b = a ∧
      ∀ x : A, x = z ∨ x = a ∨ x = b := by
  have hcard : (Finset.univ.erase z).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, h.card]
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ x : A, x ≠ z → x = a ∨ x = b := by
    intro x hx
    have : x ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩
    rw [hset] at this
    simpa using this
  have haz : a ≠ z := by
    have : a ∈ Finset.univ.erase z := by rw [hset]; simp
    exact (Finset.mem_erase.mp this).1
  have hbz : b ≠ z := by
    have : b ∈ Finset.univ.erase z := by rw [hset]; simp
    exact (Finset.mem_erase.mp this).1
  -- `σ a` is neither `z` nor `a`, hence `b`.
  have hsaz : σ a ≠ z := by
    intro hcon
    exact haz (by rw [← h.involutive a, hcon, h.fixes])
  have hsaa : σ a ≠ a := fun hcon => haz (h.onlyFixed a hcon)
  have hsab : σ a = b := (hmem (σ a) hsaz).resolve_left hsaa
  refine ⟨a, b, hab, haz, hbz, hsab, ?_, ?_⟩
  · rw [← hsab, h.involutive]
  · intro x
    by_cases hx : x = z
    · exact Or.inl hx
    · exact Or.inr (hmem x hx)

/-- **The ternary hub, closed.**  Any three-element carrier with a self-inverse
map whose only fixed point is `z` is `ZMod 3` with negation, by a transport
sending `z` to `0`. -/
theorem ternaryHub_of_involution (h : BalancedInvolution A σ z) :
    ∃ t : Transport A (ZMod 3) σ zneg, t.map z = 0 := by
  obtain ⟨a, b, hab, haz, hbz, hsab, hsba, hall⟩ := two_others h
  classical
  have e10 : (1 : ZMod 3) ≠ 0 := by decide
  have e20 : (2 : ZMod 3) ≠ 0 := by decide
  have e21 : (2 : ZMod 3) ≠ 1 := by decide
  have n0 : -(0 : ZMod 3) = 0 := by decide
  have n1 : -(1 : ZMod 3) = 2 := by decide
  have n2 : -(2 : ZMod 3) = 1 := by decide
  refine ⟨⟨⟨fun x => if x = z then 0 else if x = a then 1 else 2,
            fun n => if n = 0 then z else if n = 1 then a else b, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro x
    rcases hall x with rfl | rfl | rfl
    · simp
    · simp [haz, e10]
    · simp [hbz, Ne.symm hab, e20, e21]
  · intro n
    fin_cases n
    · simp
    · simp [haz, e10]
    · simp [hbz, Ne.symm hab, e20, e21]
  · intro x
    rcases hall x with rfl | rfl | rfl
    · simp [h.fixes, zneg, n0]
    · simp [hsab, haz, hbz, Ne.symm hab, zneg, n1]
    · simp [hsba, haz, hbz, Ne.symm hab, zneg, n2]
  · simp

/-- **Non-uniqueness, as a first-class negative.**  A balanced coordinate is
never unique: negating one gives another. -/
theorem ternaryHub_two_coordinates (h : BalancedInvolution A σ z) :
    ∃ t u : Transport A (ZMod 3) σ zneg, ∀ x, t.map x = - u.map x := by
  obtain ⟨t, -⟩ := ternaryHub_of_involution h
  refine ⟨t, ⟨t.map.trans (Equiv.neg (ZMod 3)), ?_⟩, ?_⟩
  · intro x
    simp [Equiv.neg, t.equivariant x, zneg]
  · intro x
    simp [Equiv.neg]

/-- Consequently no theorem of the form "the balanced coordinate is unique" can
hold. -/
theorem ternaryHub_not_unique (h : BalancedInvolution A σ z) :
    ¬ ∀ t u : Transport A (ZMod 3) σ zneg, ∀ x, t.map x = u.map x := by
  intro huniq
  obtain ⟨a, b, hab, haz, -, -, -, -⟩ := two_others h
  obtain ⟨t, u, hneg⟩ := ternaryHub_two_coordinates h
  have key : ∀ w : ZMod 3, w = -w → w = 0 := by decide
  have hz0 : u.map z = 0 := key _ ((huniq t u z).symm.trans (hneg z))
  have ha0 : u.map a = 0 := key _ ((huniq t u a).symm.trans (hneg a))
  exact haz (u.map.injective (by rw [ha0, hz0]))

/-! ## The eight carriers become instances

Two worked instantiations.  Each costs exactly the four `decide`s the
`BalancedInvolution` fields ask for; the transport then comes from the general
theorem rather than from a hand-written equivalence.
-/

open Integration.Ontology in
/-- The ontology carrier satisfies the hypotheses. -/
theorem epistemicTrit_balancedInvolution :
    BalancedInvolution EpistemicTrit polarity .unresolved where
  card := by decide
  involutive := by decide
  fixes := by decide
  onlyFixed := by decide

open Integration.Ontology in
/-- ...so its hub is an instance of the general theorem, not a separate result. -/
theorem epistemicTrit_hub_from_closure :
    ∃ t : Transport EpistemicTrit (ZMod 3) polarity zneg, t.map .unresolved = 0 :=
  ternaryHub_of_involution epistemicTrit_balancedInvolution

open Integration.DNAMarginTrit in
/-- The chemistry-margin carrier satisfies the hypotheses. -/
theorem chemistryMargin_balancedInvolution :
    BalancedInvolution ChemistryMargin marginPolarity .neutralMargin where
  card := by decide
  involutive := by decide
  fixes := by decide
  onlyFixed := by decide

open Integration.DNAMarginTrit in
/-- ...and so does its hub. -/
theorem chemistryMargin_hub_from_closure :
    ∃ t : Transport ChemistryMargin (ZMod 3) marginPolarity zneg,
      t.map .neutralMargin = 0 :=
  ternaryHub_of_involution chemistryMargin_balancedInvolution

deriving instance Fintype for AgdaMirror.DASHIAlgebra.Trit
deriving instance Fintype for AgdaMirror.Base369.TriTruth

/-- The algebra lane's `Trit` with digit negation. -/
theorem trit_balancedInvolution :
    BalancedInvolution AgdaMirror.DASHIAlgebra.Trit AgdaMirror.DASHIAlgebra.Trit.inv .zer where
  card := by decide
  involutive := by decide
  fixes := by decide
  onlyFixed := by decide

/-- The `Base369` tone with its reflection. -/
theorem triTruth_balancedInvolution :
    BalancedInvolution AgdaMirror.Base369.TriTruth Synthesis.ToneCore.triReflect .mid where
  card := by decide
  involutive := by decide
  fixes := by decide
  onlyFixed := by decide

/-- The 3/6/9 address digit with the codec bridge's inversion. -/
theorem digit369_balancedInvolution :
    BalancedInvolution Digit369 invert369 .d6 where
  card := by decide
  involutive := by decide
  fixes := by decide
  onlyFixed := by decide

/-- The SSP trit carrier with its polarity swap. -/
theorem sspTrit_balancedInvolution :
    BalancedInvolution SSPTrit sspTritInv .zero where
  card := by decide
  involutive := by decide
  fixes := by decide
  onlyFixed := by decide

/-- **Six of the eight hub carriers are now corollaries.**  `TritCode` is
excluded because it is a dependent record rather than a flat enumeration, and
`BTBranch` because the corpus declares no involution on it; both keep their
hand-written treatment in `Integration.TernaryHub`. -/
theorem six_carriers_from_closure :
    (∃ t : Transport AgdaMirror.DASHIAlgebra.Trit (ZMod 3)
        AgdaMirror.DASHIAlgebra.Trit.inv zneg, t.map .zer = 0) ∧
    (∃ t : Transport AgdaMirror.Base369.TriTruth (ZMod 3) Synthesis.ToneCore.triReflect zneg, t.map .mid = 0) ∧
    (∃ t : Transport Digit369 (ZMod 3) invert369 zneg, t.map .d6 = 0) ∧
    (∃ t : Transport SSPTrit (ZMod 3) sspTritInv zneg, t.map .zero = 0) ∧
    (∃ t : Transport Integration.Ontology.EpistemicTrit (ZMod 3)
        Integration.Ontology.polarity zneg, t.map .unresolved = 0) ∧
    (∃ t : Transport Integration.DNAMarginTrit.ChemistryMargin (ZMod 3)
        Integration.DNAMarginTrit.marginPolarity zneg, t.map .neutralMargin = 0) :=
  ⟨ternaryHub_of_involution trit_balancedInvolution,
   ternaryHub_of_involution triTruth_balancedInvolution,
   ternaryHub_of_involution digit369_balancedInvolution,
   ternaryHub_of_involution sspTrit_balancedInvolution,
   epistemicTrit_hub_from_closure,
   chemistryMargin_hub_from_closure⟩

end Integration.TernaryHubClosure
