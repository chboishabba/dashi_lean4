import Integration.TernaryHub
import Integration.EquivarianceObstruction

/-!
# The ontology lane's epistemic trit joins the ternary hub

`Agda/DASHI/Ontology/EpistemicTrit.agda` introduces a *seventh* three-element
carrier, independently of the six already unified in `Integration.TernaryHub`:

```agda
data EpistemicTrit : Set where
  contradicted unresolved supported : EpistemicTrit
```

together with a consensus composition `_⊗ₑ_` defined by nine clauses, and two
"binary forcing" policies into a two-element decision type.  The Agda module
proves idempotence, commutativity, associativity and absorption of `unresolved`
by exhaustive `refl`, and records two *collision* facts about the forcing
policies.  Nothing there relates the carrier to any other ternary carrier in the
corpus, and nothing there rules out a forcing policy that respects polarity.

This file supplies both, as checked Lean statements.

## What is proved

* `agree_eq_ifEq` — **the characterisation**: the nine-clause consensus table is
  exactly `fun x y => if x = y then x else unresolved`.  Every algebraic fact the
  Agda module proves clause-by-clause (`agree_idem`, `agree_comm`, `agree_assoc`,
  `agree_unresolved_left/right`, `agree_disagreement`) is a consequence.
* `epistemicHub` — an `Integration.Levels.Transport` from `EpistemicTrit` with
  its evidence polarity (swap `contradicted`/`supported`, fix `unresolved`) to
  `ZMod 3` with negation.  So the ontology carrier is the *same* balanced ternary
  digit as the six hub carriers, in the same coordinate; `epistemicHub_trit`
  states the resulting identification with `DASHI.Algebra.Trit`.
* `agree_polarity_equivariant` — the consensus operation commutes with polarity,
  so the identification is compatible with the algebra, and
  `agree_coord` transports the table into the balanced coordinate.

## What is refuted

* `agree_no_identity`, `agree_not_add`, `agree_not_mul` — consensus is *not* a
  monoid operation and is neither of `ZMod 3`'s ring operations under the hub
  coordinate.  The carrier is shared; the algebra is not.
* `no_polarity_equivariant_forcing` — **the negative result the Agda module does
  not state**: there is no polarity-equivariant map `EpistemicTrit → Bool` at
  all.  The two "collisions" recorded in Agda are therefore not accidents of the
  two chosen policies: *every* binary forcing breaks the evidence polarity,
  because polarity fixes `unresolved` while Boolean negation is fixed-point-free.
  This is the map-level obstruction
  `Integration.EquivarianceObstruction.no_equivariant_map_of_fixed_to_free`.
* `forcing_not_injective` — and every binary policy collapses two epistemic
  states, by cardinality.

## Claim boundary

`EpistemicTrit` is a three-element label type.  Nothing here is a claim about
evidence, epistemology, ontology alignment, or any real-world claim state; the
words `supported` and `contradicted` are constructor names.
-/

namespace Integration.Ontology

open Integration.Levels
open Integration.TernaryHub

/-! ## The carrier and its consensus operation -/

/-- Mirror of `DASHI.Ontology.EpistemicTrit.EpistemicTrit`. -/
inductive EpistemicTrit
  | contradicted | unresolved | supported
  deriving DecidableEq, Repr, Fintype

open EpistemicTrit

/-- Mirror of the nine-clause `_⊗ₑ_`. -/
def agree : EpistemicTrit → EpistemicTrit → EpistemicTrit
  | contradicted, contradicted => contradicted
  | supported, supported => supported
  | _, _ => unresolved

/-- **The characterisation.**  The nine-clause table is agreement-or-bottom. -/
theorem agree_eq_ifEq (x y : EpistemicTrit) :
    agree x y = if x = y then x else unresolved := by decide +kernel +revert

theorem agree_idem (x : EpistemicTrit) : agree x x = x := by decide +kernel +revert

theorem agree_comm (x y : EpistemicTrit) : agree x y = agree y x := by decide +kernel +revert

theorem agree_assoc (x y z : EpistemicTrit) :
    agree (agree x y) z = agree x (agree y z) := by decide +kernel +revert

theorem agree_unresolved_left (x : EpistemicTrit) : agree unresolved x = unresolved := by
  decide +kernel +revert

theorem agree_unresolved_right (x : EpistemicTrit) : agree x unresolved = unresolved := by
  decide +kernel +revert

/-- Disagreement of determinate states is `unresolved`: composition cannot
manufacture certainty. -/
theorem agree_disagreement : agree contradicted supported = unresolved := rfl

/-- Consensus has no identity element, so it is not a monoid operation. -/
theorem agree_no_identity : ¬ ∃ e : EpistemicTrit, ∀ x, agree e x = x := by decide +kernel +revert

/-! ## Joining the ternary hub -/

/-- Evidence polarity: swap the two determinate states, fix `unresolved`. -/
def polarity : EpistemicTrit → EpistemicTrit
  | contradicted => supported
  | unresolved => unresolved
  | supported => contradicted

theorem polarity_involutive (x : EpistemicTrit) : polarity (polarity x) = x := by
  decide +kernel +revert

/-- The balanced coordinate: `unresolved ↦ 0`, `supported ↦ 1`,
`contradicted ↦ -1`. -/
def balEpistemic : EpistemicTrit → ZMod 3
  | contradicted => -1
  | unresolved => 0
  | supported => 1

/-- The inverse coordinate. -/
def unbalEpistemic (z : ZMod 3) : EpistemicTrit :=
  if z = 0 then unresolved else if z = 1 then supported else contradicted

/-- The carriers are in bijection. -/
def balEpistemicEquiv : EpistemicTrit ≃ ZMod 3 where
  toFun := balEpistemic
  invFun := unbalEpistemic
  left_inv := by decide +kernel +revert
  right_inv := by decide +kernel +revert

theorem balEpistemic_polarity (x : EpistemicTrit) :
    balEpistemic (polarity x) = - balEpistemic x := by decide +kernel +revert

/-- **The ontology carrier is the hub carrier.**  A level-4 transport: the
evidence polarity becomes negation in the balanced coordinate. -/
def epistemicHub : Transport EpistemicTrit (ZMod 3) polarity zneg :=
  ⟨balEpistemicEquiv, balEpistemic_polarity⟩

/-- Composing with the hub identifies the ontology carrier with the algebra
lane's `Trit`, polarity for polarity. -/
def epistemicHub_trit :
    Transport EpistemicTrit AgdaMirror.DASHIAlgebra.Trit polarity AgdaMirror.DASHIAlgebra.Trit.inv :=
  epistemicHub.trans (Transport.symm tritHub)

/-- Consensus respects polarity, so the identification is compatible with the
consensus algebra as well as with the involution. -/
theorem agree_polarity_equivariant (x y : EpistemicTrit) :
    polarity (agree x y) = agree (polarity x) (polarity y) := by decide +kernel +revert

/-- The consensus table in the balanced coordinate. -/
theorem agree_coord (x y : EpistemicTrit) :
    balEpistemic (agree x y) =
      (if balEpistemic x = balEpistemic y then balEpistemic x else 0) := by
  decide +kernel +revert

/-! ## What the shared carrier does *not* transport -/

/-- Consensus is not addition in the hub coordinate. -/
theorem agree_not_add :
    ¬ ∀ x y : EpistemicTrit, balEpistemic (agree x y) = balEpistemic x + balEpistemic y := by
  decide +kernel +revert

/-- Consensus is not multiplication in the hub coordinate either. -/
theorem agree_not_mul :
    ¬ ∀ x y : EpistemicTrit, balEpistemic (agree x y) = balEpistemic x * balEpistemic y := by
  decide +kernel +revert

/-! ## Binary forcing -/

/-- The Agda module's accept-biased policy. -/
def forceAccept : EpistemicTrit → Bool
  | contradicted => false
  | unresolved => true
  | supported => true

/-- The Agda module's reject-biased policy. -/
def forceReject : EpistemicTrit → Bool
  | contradicted => false
  | unresolved => false
  | supported => true

theorem acceptPolicyCollision : forceAccept unresolved = forceAccept supported := rfl

theorem rejectPolicyCollision : forceReject unresolved = forceReject contradicted := rfl

/-- Every binary policy collapses two epistemic states. -/
theorem forcing_not_injective (f : EpistemicTrit → Bool) : ¬ Function.Injective f := by
  intro hf
  exact absurd (Fintype.card_le_of_injective f hf) (by decide +kernel)

/-- **No binary forcing is polarity-equivariant.**  This strengthens the two
collision facts from "these two policies lose information" to "every policy
breaks the polarity", and it is the reason: polarity fixes `unresolved`, while
Boolean negation has no fixed point. -/
theorem no_polarity_equivariant_forcing :
    ¬ ∃ f : EpistemicTrit → Bool, ∀ x, f (polarity x) = ! f x := by
  exact Integration.EquivarianceObstruction.no_equivariant_map_of_fixed_to_free
    (σ := polarity) (a := unresolved) rfl
    Integration.EquivarianceObstruction.fixedPointFree_not

end Integration.Ontology
