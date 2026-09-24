import Cuisine.LedgerPattern
import AgdaMirror.Base369

/-!
# The one genuine cross-domain dependency of the cuisine lane

`DASHI.Culture.Cuisine.SituatedMoleWorld` really does depend, definitionally, on
`DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge`: the record
`SituatedMoleWorld` has fields

```agda
    hyperfabricBridge    : Hyper.HyperfabricIntersectionalBodyMemoryBridge
    hyperfabricPowerAxes : List Hyper.PowerAtlasAxis
    hyperfabricPowerAxesAreCanonical :
      hyperfabricPowerAxes ≡ Hyper.canonicalPowerAtlasAxes
```

This is the only import of the cuisine lane that reaches vocabulary of the
"hyperfabric / trit / dialectic / spiral / hypervoxel / prime / p-adic" family,
so it deserves to be checked rather than described.  This file transcribes the
relevant fragment of that Agda module and separates its three kinds of content.

* **Real proof content.**  `AdmissibleInterpretiveRoute` is a genuine
  `Set`-valued guard: it is `⊤` on the candidate route and the empty type on the
  six promotion routes, and the Agda module discharges six absurdity lemmas.
  `admissible_iff_candidate` and `exists_unique_admissible` state the same fact
  once and in a stronger form: the candidate route is the *only* admissible one.
* **Real but weaker content.**  The eight "triadic relation surfaces" are kept
  apart by their names: `triadicRelationSurfaceName` is injective
  (`triadicRelationSurfaceName_injective`), which is the checkable core of the
  informal claim that the vocabulary is not collapsed.  The twelve power axes
  are likewise pairwise distinct and the canonical atlas lists each once
  (`canonicalPowerAtlasAxes_nodup`).
* **No content.**  The cuisine-side facet — a list of axes together with a proof
  that it is *the* canonical list — is a singleton type
  (`HyperfabricFacet.instUnique`).  So the hyperfabric dependency of the mole
  world adds a fixed constant, not a choice, and the accompanying
  `Bool`-with-`= true` row flags are contentless in the sense of
  `Cuisine.LedgerPattern`.

Finally, the negative result that matters for the corpus as a whole:
`no_injective_trit_labelling` shows the eight triad surfaces cannot be injected
into the ternary tone carrier `AgdaMirror.Base369.TriTruth` at all.  So the
occurrence of the word "trit" among the surface *names* is not, and cannot be
upgraded to, an identification of these surfaces with the ternary structure used
by the `Synthesis` spine.  Compare `Cuisine.ToneSeparation`, which rules out the
identification on the cuisine safety carrier, where the cardinalities do match.
-/

namespace Cuisine.HyperfabricGuard

open AgdaMirror.Base369 (TriTruth HexTruth)

/-- The mirrored ternary tone carrier is finite; `AgdaMirror.Base369` derives
only decidable equality for it. -/
instance : Fintype TriTruth := ⟨{TriTruth.low, TriTruth.mid, TriTruth.high}, fun x => by cases x <;> decide⟩

instance : Fintype HexTruth :=
  ⟨{HexTruth.h0, HexTruth.h1, HexTruth.h2, HexTruth.h3, HexTruth.h4, HexTruth.h5}, fun x => by cases x <;> decide⟩

/-! ## Interpretive routes: the guard with actual proof content -/

/-- The seven interpretive routes of the Agda guard module. -/
inductive InterpretiveRoute
  | candidate
  | neutralTriadUniversalism
  | monocultureCompression
  | socialTruthProof
  | clinicalAuthority
  | legalAuthority
  | educationalAuthority
  deriving DecidableEq, Fintype, Repr

open InterpretiveRoute

/-- `AdmissibleInterpretiveRoute` of the Agda module, transcribed.  In Agda the
codomain is `Set`, with `⊤` on the candidate route and an empty type `Never`
elsewhere; in Lean this is a `Prop`-valued predicate with the same content. -/
def Admissible : InterpretiveRoute → Prop
  | candidate => True
  | neutralTriadUniversalism => False
  | monocultureCompression => False
  | socialTruthProof => False
  | clinicalAuthority => False
  | legalAuthority => False
  | educationalAuthority => False

instance (r : InterpretiveRoute) : Decidable (Admissible r) := by
  cases r <;> unfold Admissible <;> infer_instance

/-- The Agda module's positive lemma `candidateInterpretiveRouteAdmissible`. -/
theorem candidate_admissible : Admissible candidate := trivial

/-- The Agda module's six rejection lemmas, in one statement: admissibility is
*exactly* being the candidate route.  Nothing may be promoted through the
guard. -/
theorem admissible_iff_candidate {r : InterpretiveRoute} :
    Admissible r ↔ r = candidate := by
  cases r <;> simp [Admissible]

/-- Consequently the guard admits exactly one route. -/
theorem exists_unique_admissible : ∃! r : InterpretiveRoute, Admissible r :=
  ⟨candidate, candidate_admissible, fun _ h => admissible_iff_candidate.mp h⟩

/-- In particular no promotion route — social-truth, clinical, legal or
educational authority — is admissible. -/
theorem no_authority_promotion :
    ¬ Admissible socialTruthProof ∧ ¬ Admissible clinicalAuthority ∧
      ¬ Admissible legalAuthority ∧ ¬ Admissible educationalAuthority := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Admissible]

/-! ## Triadic relation surfaces: separated by name, not by structure -/

/-- The eight "triadic relation surfaces" the guard module keeps apart. -/
inductive TriadSurface
  | dialectic | spiral | hypervoxel | hyperfabric | trit | stage | prime | padic
  deriving DecidableEq, Fintype, Repr

open TriadSurface

/-- `triadicRelationSurfaceName`, transcribed verbatim. -/
def surfaceName : TriadSurface → String
  | dialectic => "dialectic-triad-surface"
  | spiral => "spiral-triad-surface"
  | hypervoxel => "hypervoxel-triad-surface"
  | hyperfabric => "hyperfabric-triad-surface"
  | trit => "trit-triad-surface"
  | stage => "stage-triad-surface"
  | prime => "prime-triad-surface"
  | padic => "p-adic-triad-surface"

/-- The checkable core of "this vocabulary is not collapsed": the eight surfaces
receive eight distinct names.  The Agda module lists the names but never states
their distinctness. -/
theorem surfaceName_injective : Function.Injective surfaceName := by decide

/-- Being separated by name is all that is established: there are exactly eight
surfaces, with no further structure relating them. -/
theorem card_triadSurface : Fintype.card TriadSurface = 8 := by decide

/-- **The vocabulary is not a trit structure.**  Eight surfaces cannot be
embedded in the three-element ternary tone carrier, so no reading of the surface
family as ternary truth values is even injective, let alone structure
preserving.  The appearance of `trit` as one of the eight *names* is therefore
not a link to `AgdaMirror.Base369`. -/
theorem no_injective_trit_labelling :
    ¬ ∃ f : TriadSurface → TriTruth, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h : Fintype.card TriadSurface ≤ Fintype.card TriTruth :=
    Fintype.card_le_of_injective f hf
  rw [card_triadSurface] at h
  have : Fintype.card TriTruth = 3 := by decide
  omega

/-- Neither is it a hexadic or nonadic one: the same cardinality obstruction
rules out an injection into `HexTruth` (six elements).  Only carriers of at
least eight elements could receive the surface family. -/
theorem no_injective_hex_labelling :
    ¬ ∃ f : TriadSurface → AgdaMirror.Base369.HexTruth, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h : Fintype.card TriadSurface ≤ Fintype.card AgdaMirror.Base369.HexTruth :=
    Fintype.card_le_of_injective f hf
  rw [card_triadSurface] at h
  have : Fintype.card AgdaMirror.Base369.HexTruth = 6 := by decide
  omega

/-! ## The power atlas, and the cuisine-side facet -/

/-- The twelve axes of the intersectional power atlas. -/
inductive PowerAtlasAxis
  | race | classAxis | gender | sexuality | disability | neurotype
  | religion | coloniality | law | land | family | institution
  deriving DecidableEq, Fintype, Repr

open PowerAtlasAxis

/-- `powerAtlasAxisName`, transcribed verbatim. -/
def axisName : PowerAtlasAxis → String
  | race => "race-power-axis"
  | classAxis => "class-power-axis"
  | gender => "gender-power-axis"
  | sexuality => "sexuality-power-axis"
  | disability => "disability-power-axis"
  | neurotype => "neurotype-power-axis"
  | religion => "religion-power-axis"
  | coloniality => "coloniality-power-axis"
  | law => "law-power-axis"
  | land => "land-power-axis"
  | family => "family-power-axis"
  | institution => "institution-power-axis"

theorem axisName_injective : Function.Injective axisName := by decide

/-- `canonicalPowerAtlasAxes`, transcribed verbatim. -/
def canonicalPowerAtlasAxes : List PowerAtlasAxis :=
  [race, classAxis, gender, sexuality, disability, neurotype,
   religion, coloniality, law, land, family, institution]

/-- The canonical atlas lists each of the twelve axes exactly once — it is an
enumeration, which the Agda module asserts only by construction. -/
theorem canonicalPowerAtlasAxes_nodup : canonicalPowerAtlasAxes.Nodup := by decide

theorem canonicalPowerAtlasAxes_length : canonicalPowerAtlasAxes.length = 12 := by decide

theorem canonicalPowerAtlasAxes_complete (a : PowerAtlasAxis) :
    a ∈ canonicalPowerAtlasAxes := by
  cases a <;> decide

/-- The hyperfabric facet of `SituatedMoleWorld`: a list of power axes together
with a proof that it is the canonical one. -/
structure HyperfabricFacet where
  powerAxes : List PowerAtlasAxis
  powerAxesAreCanonical : powerAxes = canonicalPowerAtlasAxes

/-- **The facet carries no choice.**  Together with its canonicity proof, the
axis field of the situated mole world is a singleton type: the cuisine-side
hyperfabric dependency contributes a fixed constant, exactly like the
`Bool`-with-`= false` ledgers of `Cuisine.LedgerPattern`. -/
instance : Unique HyperfabricFacet where
  default := ⟨canonicalPowerAtlasAxes, rfl⟩
  uniq := by rintro ⟨_, rfl⟩; rfl

/-- Restated as an equivalence, for use alongside
`Cuisine.LedgerPattern.cuisinePropositionBoundaryEquivUnit`. -/
def hyperfabricFacetEquivUnit : HyperfabricFacet ≃ Unit := Equiv.equivPUnit _

/-! ## Summary of the cuisine ↔ hyperfabric edge -/

/-- The cuisine lane's single cross-domain definitional dependency, audited.

1. the guard it imports really does reject every promotion route
   (`admissible_iff_candidate`);
2. the vocabulary it keeps apart is kept apart only by naming
   (`surfaceName_injective`);
3. the part of it the cuisine record actually stores is contentless
   (`HyperfabricFacet` is a singleton);
4. and none of it is a ternary structure (`no_injective_trit_labelling`). -/
theorem hyperfabric_edge_audit :
    (∃! r : InterpretiveRoute, Admissible r) ∧
      Function.Injective surfaceName ∧
      (∀ h : HyperfabricFacet, h = default) ∧
      ¬ ∃ f : TriadSurface → TriTruth, Function.Injective f :=
  ⟨exists_unique_admissible, surfaceName_injective, fun _ => Subsingleton.elim _ _,
    no_injective_trit_labelling⟩

end Cuisine.HyperfabricGuard
