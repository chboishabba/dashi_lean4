import RequestProject.Publish
import RequestProject.Sync
import RequestProject.Archive
import RequestProject.Generated.DouglasAdams

/-!
# The publication layer on the worked fragment

The general theorems of `RequestProject.Publish`, `RequestProject.Sync` and
`RequestProject.Archive` say what publishing, gossiping and archiving guarantee.
This file runs them on the downloaded fragment about Douglas Adams, so the
guarantees are exhibited on real data rather than only in the abstract:

* the fragment is safe to publish, and a round trip through the published JSON
  Lines file returns it unchanged;
* its published file has exactly one row per item, level and statement;
* its archive deposit re-imports to the same base and its manifest checks out;
* two replicas that each hold half of the statements *disagree*, and after one
  round of gossip they agree again and the pooled state entails the whole
  fragment — nothing was lost by splitting it up.
-/

namespace Wikidata
namespace PublishExamples

open Wikidata.Cli Wikidata.Publish

/-- The worked fragment: what `wikidata fetch Q42 --depth 3` downloaded. -/
abbrev douglas : KB := Generated.DouglasAdams.kb

/-! ### Publishing -/

/-- Every field of every published row is safe to put in a JSON array. -/
theorem douglas_jsonSafe : jsonSafeKB douglas = true := by native_decide

/-- **A round trip through the published file changes nothing.** -/
theorem douglas_jsonl_roundTrip : parseJsonl? (jsonlOfKB douglas) = some douglas :=
  parseJsonl?_jsonlOfKB douglas douglas_jsonSafe

/-- The fragment is also safe to write in the project's own format. -/
theorem douglas_clean : KB.cleanB douglas = true := by native_decide

/-- A round trip through the `.wdkb` file changes nothing either. -/
theorem douglas_wdkb_roundTrip : parseKB? (renderKB douglas) = some douglas :=
  parseKB?_renderKB douglas douglas_clean

/-- The published file carries 64 rows: the header, 21 items, 21 levels and no
disjointness, plus the 12 `subclass of` and 9 `instance of` statements. -/
theorem douglas_rows : (kbRecs douglas).length = 64 := by native_decide

/-- …which is what `Publish.length_kbRecs` predicts. -/
example : (kbRecs douglas).length =
    1 + douglas.items.length + douglas.levels.length + douglas.sub.length +
      douglas.inst.length + douglas.disj.length := length_kbRecs douglas

/-! ### Archiving -/

/-- **The deposit re-imports to the base it was made from.** -/
theorem douglas_archive_roundTrip :
    Archive.importKB? (Archive.bundleOf douglas).files = some douglas :=
  Archive.importKB?_bundleOf douglas douglas_clean

/-- The manifest of the deposit is honest. -/
theorem douglas_archive_manifest :
    Archive.checkManifest (Archive.bundleOf douglas).files
      (Archive.manifestRows (Archive.bundleOf douglas).files) = true :=
  Archive.checkManifest_bundleOf douglas

/-! ### Two replicas that drift apart -/

/-- One peer that heard only the first half of the statements. -/
def replicaA : KB :=
  { douglas with name := "peer A", sub := douglas.sub.take 6, inst := douglas.inst.take 4 }

/-- Another peer that heard only the second half. -/
def replicaB : KB :=
  { douglas with name := "peer B", sub := douglas.sub.drop 6, inst := douglas.inst.drop 4 }

theorem replicaA_wellFormed : replicaA.wellFormed = true := by native_decide
theorem replicaB_wellFormed : replicaB.wellFormed = true := by native_decide

/-- The replicas really have drifted: neither entails the other. -/
theorem replicas_disagree :
    KB.Equiv replicaA replicaB = false ∧ KB.Equiv replicaB replicaA = false := by
  native_decide

/-- The pooled state knows the whole fragment again. -/
theorem pool_entails_douglas : (KB.pool [replicaA, replicaB]).Entails douglas = true := by
  native_decide

/-- **After one round of gossip the replicas agree**, as
`KB.gossip_pairwise_equiv` says they must. -/
theorem gossip_converges :
    ((KB.gossip [replicaA, replicaB]).all fun a =>
      (KB.gossip [replicaA, replicaB]).all fun b => KB.Equiv a b) = true := by
  native_decide

/-- And every replica then entails the whole fragment. -/
theorem gossip_keeps_everything :
    ((KB.gossip [replicaA, replicaB]).all fun a => a.Entails douglas) = true := by
  native_decide

/-! ### Content addresses -/

/-- The content address the tool publishes for this fragment. -/
theorem douglas_cid : cid douglas = "wdkb1-d85a9bb9e764ac9a" := by native_decide

end PublishExamples
end Wikidata
