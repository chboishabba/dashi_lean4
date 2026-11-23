import RequestProject.Slr.WikipediaArticleProof
import RequestProject.Cli.Import

/-!
Q207/article-title source identity weld.

The existing JMD Wikipedia source checker proves exact parser/source
observations. Original JMD Cli.Import opens an independently acquired
Wikidata Special:EntityData JSON and extracts an enwiki sitelink.

A positive result means the two retained documents present the same
QID/title coordinate at their respective revisions. It is NOT proof of
same-time snapshots, occurrence or the truth of the article's claims.

Original JMD entity importer: meta-introspector.
-/

namespace Wikidata
namespace Slr
namespace GwbArticleIdentity

open Lean

private def string? (j : Json) (key : String) : Option String :=
  (j.getObjValAs? String key).toOption

/-- No hard-coded claim that an arbitrary title identifies a person.
    Verify the independently imported Wikidata entity matches the root QID
    and has the exact English Wikipedia sitelink requested by the caller. -/
def checkSitelink (qid title : String) (wikidata : Json) : Bool :=
  let raw := ((wikidata.getObjVal? "entities").toOption.getD Json.null)
  let entity := (raw.getObjVal? qid).toOption.getD Json.null
  string? entity "id" == some qid &&
  Cli.entityEnwikiTitle entity == some title

/-- The GWB root has the pinned original Wikipedia revision and source
    checked by JMD, and an independently imported Wikidata Q207 sitelink.
    This is a two-source correspondence, NOT historical claim equivalence. -/
def checkGwbRootIdentity (article : String)
    (slr projection wikidata : Json) : Bool :=
  ArticleProof.checkProjection article slr projection &&
  string? slr "revision_ref" == some "enwiki-revid:1385850169" &&
  string? projection "wikidata_item_qid" == some "Q207" &&
  string? projection "source_revision_ref" ==
    some "enwiki-revid:1385850169" &&
  checkSitelink "Q207" "George W. Bush" wikidata

structure CheckedGwbRootIdentity
    (article : String) (slr projection wikidata : Json) where
  checked : checkGwbRootIdentity article slr projection wikidata = true

theorem checkedGwbRootSourceAndSitelink
    {article : String} {slr projection wikidata : Json}
    (h : CheckedGwbRootIdentity article slr projection wikidata) :
    checkGwbRootIdentity article slr projection wikidata = true :=
  h.checked

end GwbArticleIdentity
end Slr
end Wikidata
