/-!
Source-bounded Iranian revolutionary intellectual genealogy mirror.

The positive result is field-level mediated continuity, not a fabricated direct
person-to-person influence edge.
-/

namespace AgdaMirror.Governance.IranianRevolutionaryIntellectualGenealogy

inductive GenealogyNode
  | marxianLeftField
  | fanonianAnticolonialField
  | iranianThirdWorldistField
  | alEAhmadWestoxicationField
  | shariatiIslamicRevolutionarySynthesis
  | iranianRevolutionaryGeneration
  | khomeiniAntiWestRevolutionaryDiscourse
  | islamicRepublicRevolutionaryGrammar
  deriving DecidableEq, Repr

inductive EdgeStrength
  | directTextualInfluence
  | documentedIntellectualInfluence
  | fieldLevelContinuity
  | structuralConvergence
  deriving DecidableEq, Repr

structure GenealogyEdge where
  from : GenealogyNode
  to : GenealogyNode
  strength : EdgeStrength
  sourceReceipt : String
  establishesPersonalInfluence : Bool := false
  establishesExactConceptIdentity : Bool := false

def fanonToShariati : GenealogyEdge :=
  ⟨.fanonianAnticolonialField, .shariatiIslamicRevolutionarySynthesis,
   .documentedIntellectualInfluence,
   "Gould/POMEPS: Fanon as major inspiration/template for Shariati; disputed correspondence excluded"⟩

def marxianFieldToShariati : GenealogyEdge :=
  ⟨.marxianLeftField, .shariatiIslamicRevolutionarySynthesis,
   .documentedIntellectualInfluence,
   "Boroujerdi/Cambridge: Shariati drew liberally from Marxism in constructing activist Islam"⟩

def thirdWorldismToShariati : GenealogyEdge :=
  ⟨.iranianThirdWorldistField, .shariatiIslamicRevolutionarySynthesis,
   .fieldLevelContinuity,
   "Matin-Asgari: Iranian socialist/Third-Worldist/Islamic-Marxist intellectual field"⟩

def shariatiToRevolutionaryGeneration : GenealogyEdge :=
  ⟨.shariatiIslamicRevolutionarySynthesis, .iranianRevolutionaryGeneration,
   .documentedIntellectualInfluence,
   "Saffari/Cambridge: Shariati inspired many in the revolutionary generation"⟩

def iranianLeftToKhomeiniWestGrammar : GenealogyEdge :=
  ⟨.marxianLeftField, .khomeiniAntiWestRevolutionaryDiscourse,
   .fieldLevelContinuity,
   "Kamrava/Cambridge: Khomeini's West/neocolonial discourse was not a radical departure from the Iranian Left"⟩

def westoxicationToThirdWorldistField : GenealogyEdge :=
  ⟨.alEAhmadWestoxicationField, .iranianThirdWorldistField,
   .structuralConvergence,
   "Hanson 1983: Westoxication critique situated in a Third-World/dependency-style problem field"⟩

def canonicalFieldEdges : List GenealogyEdge := [
  fanonToShariati,
  marxianFieldToShariati,
  thirdWorldismToShariati,
  shariatiToRevolutionaryGeneration,
  iranianLeftToKhomeiniWestGrammar,
  westoxicationToThirdWorldistField
]

theorem all_edges_block_personal_influence_promotion :
    ∀ e ∈ canonicalFieldEdges,
      e.establishesPersonalInfluence = false ∧
      e.establishesExactConceptIdentity = false := by
  intro e h
  simp [canonicalFieldEdges] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end AgdaMirror.Governance.IranianRevolutionaryIntellectualGenealogy
