import RequestProject.Modules
import RequestProject.Examples

/-!
# Module extraction on the worked Wikidata fragment

The extraction of `RequestProject.Modules` run on `Wikidata.wdCore`: the module about
Douglas Adams (`Q42`) keeps the chain `human ⊑ person ⊑ entity` and the metaclass tower
above `human`, but drops `film` (`Q11424`) and with it the declared disjointness, since
nothing about Douglas Adams depends on them. The extracted module is again valid, and it
derives exactly the same facts about `Q42` as the whole fragment.
-/

namespace Wikidata
namespace Examples

open KB

/-- The module of the fragment about Douglas Adams. -/
def adamsModule : KB := wdCore.moduleOf [Q "Q42"]

/-- Extraction keeps the six items Douglas Adams depends on and drops `film`. -/
theorem adamsModule_items :
    adamsModule.items =
      [Q "Q42", Q "Q5", Q "Q215627", Q "Q35120", Q "Q55983715", Q "Q19478619"] := by
  decide

/-- `film` is not in the module, and neither is the disjointness statement about it. -/
theorem adamsModule_drops_film :
    Q "Q11424" ∉ adamsModule.items ∧ adamsModule.disj = [] := by
  decide

/-- The extracted module passes the validator, as `Wikidata.KB.moduleOf_valid` predicts. -/
theorem adamsModule_valid : adamsModule.valid = true := by decide

/-- The module still derives that Douglas Adams is an entity. -/
theorem adamsModule_adams_entity : adamsModule.isInstanceOf (Q "Q42") (Q "Q35120") = true := by
  decide

/-- Conservativity, checked by computation on this fragment: the module and the whole
base agree on every derived `instance of` fact about Douglas Adams. -/
theorem adamsModule_conservative :
    wdCore.items.all (fun c =>
      adamsModule.isInstanceOf (Q "Q42") c == wdCore.isInstanceOf (Q "Q42") c) = true := by
  decide

/-- The same, as an instance of the general theorem rather than by computation. -/
theorem adamsModule_conservative' (c : Qid) :
    adamsModule.isInstanceOf (Q "Q42") c = wdCore.isInstanceOf (Q "Q42") c :=
  moduleOf_isInstanceOf (valid_wellFormed wdCore_valid)
    (seed_mem_moduleItemsF (List.mem_singleton_self _)) c

/-- The module about `film` alone is just `film`: nothing in the fragment lies above it. -/
theorem filmModule_items : (wdCore.moduleOf [Q "Q11424"]).items = [Q "Q11424"] := by decide

end Examples
end Wikidata
