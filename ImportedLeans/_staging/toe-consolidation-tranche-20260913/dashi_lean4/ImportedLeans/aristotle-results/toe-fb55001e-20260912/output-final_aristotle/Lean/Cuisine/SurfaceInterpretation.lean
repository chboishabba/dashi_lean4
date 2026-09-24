import Cuisine.HyperfabricGuard
import Cuisine.NineSheet
import Cuisine.SpiralCarrier

/-!
# The guard's semantic surfaces, interpreted in the implementation types

`DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge` — the cuisine lane's
one cross-domain definitional import — enumerates eight *semantic* surfaces
named `dialectic`, `spiral`, `hypervoxel`, `hyperfabric`, `trit`, `stage`,
`prime`, `p-adic`.  `Cuisine.HyperfabricGuard` proves the negative facts about
that enumeration: the eight surfaces are separated only by their names, and they
do not inject into any ternary or hexadic carrier, so the family cannot itself be
read as ternary structure.

What was missing, and is supplied here, is the *other* direction: an explicit
map from each semantic surface to the implementation carrier of the same name in
this repository, with the identification of that carrier proved.  This is the
"which actual type does this word denote" table, in typed form.

* `interpret : TriadSurface → SurfaceCarrier` — the assignment, which is
  **total**: every one of the eight names has a referent, `spiral` included
  (`Cuisine.SpiralCarrier`).
* `carrierCard` and `carrierCard_eq` — each carrier's cardinality, matched
  against the real `Fintype.card` of the implementation type it names
  (`Trit`, `LogicTlurey.Stage`, `Stage6`, `SSP`, a depth-nine ternary sheet,
  `MaskSSP`, `Fabric`).
* `interpret_injective` — the assignment is injective, so the eight names denote
  eight *different* things: the vocabulary is non-redundant, which is the
  positive form of the guard's non-collapse claim.
* `spiral_matched` — the referent of `spiral` is the four-element Klüver
  form-constant carrier of `Agda/DASHI/Cognition/KlueverFormConstantProjection`,
  of which `spiral` is one value.  An earlier version of this file recorded
  `spiral` as unmatched; that was a gap in the search, not in the corpus.
* `carrierCard_nodup_except_stage_spiral` — honesty clause: the eight carriers
  have pairwise distinct sizes *except* for `stage` and `spiral`, which are both
  four-element types (`LogicTlurey.Stage` and `KlueverForm`).  So cardinality
  separates six of the eight names from all the others but cannot separate those
  two from each other, even though they are different types.

Boundary: this is a naming table with proved cardinalities.  Assigning the word
`hyperfabric` to the type `Fabric` does not make the guard's informal claims
about that word true; it only makes the reference explicit and checkable.
-/

namespace Cuisine.SurfaceInterpretation

open AgdaMirror.DASHIAlgebra (Trit Stage6)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Cuisine.HyperfabricGuard (TriadSurface)
open Cuisine.HyperfabricGuard.TriadSurface
open Cuisine.NineSheet (Supported card_supported)
open Cuisine.SpiralCarrier (KlueverForm card_klueverForm)

instance : Fintype Stage6 :=
  ⟨{.affirmed, .denied, .affirmedAndDenied, .inexpressible, .affirmedInexpressible,
    .deniedInexpressible}, fun x => by cases x <;> decide⟩

instance : Fintype AgdaMirror.LogicTlurey.Stage :=
  ⟨{.seed, .counter, .resonance, .overflow}, fun x => by cases x <;> decide⟩

/-- The implementation carriers this repository actually defines. -/
inductive SurfaceCarrier
  | tritCarrier | stage4Carrier | form4Carrier | stage6Carrier | prime15Carrier
  | sheet9Carrier | mask15Carrier | fabric15Carrier
  deriving DecidableEq, Fintype, Repr

open SurfaceCarrier

/-- **The interpretation table.**  Each semantic surface of the guard is sent to
the implementation carrier of the same name. -/
def interpret : TriadSurface → SurfaceCarrier
  | dialectic => stage6Carrier
  | spiral => form4Carrier
  | hypervoxel => sheet9Carrier
  | hyperfabric => fabric15Carrier
  | trit => tritCarrier
  | stage => stage4Carrier
  | prime => prime15Carrier
  | padic => mask15Carrier

/-- The size of each carrier. -/
def carrierCard : SurfaceCarrier → ℕ
  | tritCarrier => 3
  | stage4Carrier => 4
  | form4Carrier => 4
  | stage6Carrier => 6
  | prime15Carrier => 15
  | sheet9Carrier => 19683
  | mask15Carrier => 32768
  | fabric15Carrier => 14348907

/-- **The carriers are the real implementation types.**  Each stated cardinality
is the `Fintype.card` of the type the surface names. -/
theorem carrierCard_eq :
    carrierCard tritCarrier = Fintype.card Trit ∧
      carrierCard stage4Carrier = Fintype.card AgdaMirror.LogicTlurey.Stage ∧
      carrierCard form4Carrier = Fintype.card KlueverForm ∧
      carrierCard stage6Carrier = Fintype.card Stage6 ∧
      carrierCard prime15Carrier = Fintype.card SSP ∧
      carrierCard mask15Carrier = Fintype.card MaskSSP ∧
      carrierCard fabric15Carrier = Fintype.card Fabric := by
  refine ⟨rfl, rfl, (card_klueverForm).symm, rfl, rfl, ?_, ?_⟩
  · rw [card_maskSSP]; norm_num [carrierCard]
  · rw [card_fabric]; norm_num [carrierCard]

/-- The depth-nine sheet carrier: for any nine of the fifteen base points, the
sections supported there number `19683`, matching `carrierCard sheet9Carrier`. -/
theorem carrierCard_sheet9 (s : Finset SSP) (hs : s.card = 9) :
    carrierCard sheet9Carrier = Fintype.card (Supported s) := by
  rw [card_supported, hs]
  norm_num [carrierCard]

/-- **The eight names denote eight different things.** -/
theorem interpret_injective : Function.Injective interpret := by decide

/-- `spiral`'s referent is the Klüver form-constant carrier, of which `spiral`
is one of the four values.  (An earlier version of this file recorded `spiral`
as having no referent; see `Cuisine.SpiralCarrier`.) -/
theorem spiral_matched : interpret spiral = form4Carrier := rfl

/-- **Honesty clause.**  Cardinality separates every pair of distinct surfaces
except `stage` and `spiral`, whose carriers are both four-element types. -/
theorem carrierCard_nodup_except_stage_spiral {a b : TriadSurface}
    (hab : a ≠ b) (h : carrierCard (interpret a) = carrierCard (interpret b)) :
    (a = stage ∧ b = spiral) ∨ (a = spiral ∧ b = stage) := by
  revert hab h
  revert a b
  decide

/-- The two four-element carriers really are different types: the Tlurey stage
lattice and the Klüver form constants. -/
theorem stage_spiral_carriers_differ : interpret stage ≠ interpret spiral := by decide

end Cuisine.SurfaceInterpretation
