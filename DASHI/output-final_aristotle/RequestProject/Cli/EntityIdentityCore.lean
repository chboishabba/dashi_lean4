/-!
# Lightweight JMD EntityData source identity fields

Source-owner extraction of the original meta-introspector JMD
Cli.Import.entityLabelIn and Cli.Import.entityEnwikiTitle definitions.
This module depends on Lean JSON only; Cli.Import imports this exact
implementation so the small source-field check and full JMD importer
cannot diverge. This is NOT a semantic actor/referent or KB proof.
-/
import Lean.Data.Json

namespace Wikidata
namespace Cli

open Lean (Json)

/-- The label of an entity in one language of the original JSON, if present. -/
def entityLabelIn (j : Json) (lang : String) : Option String :=
  ((j.getObjVal? "labels").bind (·.getObjVal? lang) |>.bind
    (·.getObjValAs? String "value")).toOption

/-- The enwiki title in the original EntityData object, if present. -/
def entityEnwikiTitle (j : Json) : Option String :=
  ((j.getObjVal? "sitelinks").bind (·.getObjVal? "enwiki") |>.bind
    (·.getObjValAs? String "title")).toOption

end Cli
end Wikidata
