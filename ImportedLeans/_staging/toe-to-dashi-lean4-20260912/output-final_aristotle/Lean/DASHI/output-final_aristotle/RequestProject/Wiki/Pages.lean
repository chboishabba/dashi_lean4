import RequestProject.Wiki.Registry
import RequestProject.Wiki.Generate
import RequestProject.Generated.UpperOntology
import RequestProject.Generated.Glossary
import RequestProject.Cli.Query

/-!
# Pages

Two things live here: a page **imported** from wikidata.org, and pages
**generated** from the formalized ontology.

## The imported page

`Wikidata.Wiki.Pages.wikiProjectOntology` is the wikitext of
`Wikidata:WikiProject Ontology`, as exported from wikidata.org, parsed into a
`Wikidata.Wiki.Page` at compile time by `wikipage!`.  Three theorems say that the
import is faithful and that the page is understood:

* `wikiProjectOntology.render_eq` — printing the parsed page returns the exported
  wikitext, character for character (this is the general theorem
  `Wikidata.Wiki.render_parsePage` specialised by evaluation);
* `wikiProjectOntology_clean` — the page is hygienic, so it is also true that
  reading its wikitext again gives the same page back
  (`wikiProjectOntology_reparse`);
* `wikiProjectOntology_uses_registered` — every template the page calls is one of
  the eight documented in `RequestProject.Wiki.Registry`.

## The generated pages

`Wikidata.Wiki.Pages.upperOntologyIndex` lists the items of the upper-ontology
fragment `Wikidata.Generated.UpperOntology.kb`, with the label the glossary gives
each of them, as calls to `{{Q}}`; `Wikidata.Wiki.Pages.propertyIndex` does the
same for the properties of the glossary, as calls to `{{P}}`.  Both are built by
the verified generator of `RequestProject.Wiki.Generate`, so both come with the
guarantee that the wikitext they print reads back as the very page that was
generated — no label can smuggle markup into the result.

`wikidata wiki` writes all three pages to `pages/`.
-/

namespace Wikidata
namespace Wiki
namespace Pages

open Wikidata.Generated

/-! ## The imported page -/

wikipage! wikiProjectOntology := "<div style=\"box-shadow: 0 0 .3em #999999; border-radius: .2em; margin: 0 0 2em 0; padding: 1px;\">\n<div style=\"background: #339966; border-radius: .2em; color: #FFFFFF; padding: .4em .8em .5em; text-align: center;\">\n<span style=\"font-size: 1.3em;\">WikiProject Ontology</span>\n</div>\n<div style=\"text-align: left; padding: 1em; border-right: 1px solid #BBBBBB\">\n[[File:Wikiproject Ontology Logo WO PNG.png|200px|frameless|right]]\n<br />\n\nThe Wikidata Ontology organizes the entities in Wikidata into groups, or classes, such as {{Q|Q5}} or {{Q|Q223557}} or {{Q|Q16889133}}.\nAlmost every entity in Wikidata is an {{P|P31}} one or more classes.\n\nThe '''WikiProject [[Q324254|Ontology]]''' aims:\n* to improve the Wikidata ontology,\n* to help editors understand the Wikidata ontology,\n* to answer questions about the Wikidata Ontology,\n* to support a broad semantic interoperability between notable ontologies like DOLCE, BFO, SUMO, Lemon, RDA, etc.,\n* to build consensus around the main branches of our [http://tools.wmflabs.org/wikidata-todo/tree.html?q=Q35120&rp=279&lang=en&method=list&depth=2 core class tree] and how they relate to each other, and\n* to gain a deep understanding about the meaning of our [[Q3882785|upper ontology]] and to transfer this knowledge to others in practical terms.\n\nTo ask a question about the Wikidata Ontology or to get guidance on how to work with the ontology, add a topic to [[Wikidata_talk:WikiProject_Ontology| the project's discussion page]] or\npost in the project's [https://t.me/+AZv0cRaY2oM2MjAx Telegram group].\n\nFor specific subject areas, the class hierarchy and properties for that area may be covered in detail on a WikiProject page devoted to that subject - for example [[Wikidata:WikiProject Books|WikiProject Books]], [[Wikidata:WikiProject Names|WikiProject Names]] or [[Wikidata:WikiProject Chemistry|WikiProject Chemistry]].\n\n== Ongoing and Recent Activities ==\n\nThe [[Wikidata:WikiProject_Ontology/Ontology_Course|Wikidata Ontology Course]] is an eight-week course, with exercises and a project.  The first offering was run during May and June 2025.  The second offering is being run in May and June of 2026.  A third offering is being planned for Fall of 2026, provided that funding can be arranged.\nThe slides for all sessions of the first two offerings are available on the course page.\nPart of participating in the course is to participate in a project related to the Wikidata Ontology.  Information on the projects, many of which are continuing after the end of the course, is [[Wikidata:WikiProject_Ontology/Ontology_Course#Projects|available]].  \n\nThe [[Wikidata:WikiProject Ontology/Cleaning Task Force|Cleaning Task Force]] meets most weeks at 11:30am ET (UTC-4 during US daylight savings time and UTC-5 otherwise).  The goal of the task force is to improve and extend the Wikidata ontology. For more information see the task force page.\n\nThe [[Wikidata:WikiProject Ontology/Mereology Task Force|Mereology Task Force]] was set up to improve the modeling of part-whole relationships in Wikidata.  This task force is now disbanded.\n\n== Communications ==\n* [https://t.me/+AZv0cRaY2oM2MjAx Telegram group]\n* [https://phabricator.wikimedia.org/tag/wikidata-wikiproject-ontology/ Phabricator project]\n* [https://calendar.google.com/calendar/embed?src=90c4d393de6b606fdb90ba6da1f7c1cc7afdd084df7776c02e55170620807843%40group.calendar.google.com Online meeting calendar]\n\n==Past Efforts==\n* [[Wikidata:WikiProject_WordNet|WordNet-Wikidata Mappings]]\n* [[Wikidata:WikiProject Government|WikiProject Government]]\n* [[Wikidata:WikiProject_Ontology/Modelling Travel|Modelling Travel]]\n* [[Wikidata:WikiProject_Ontology/Mapping_Wikidata_To_BFO|Mapping Wikidata To BFO]]\n* Wikidata Ontology Course Projects\n** [[Wikidata:WikiProject Ontology/Ontology Course/Books|Books]]\n** [[Wikidata:WikiProject Ontology/Ontology Course/Project to enhance Wikidata using QUDT|Project to enhance Wikidata using QUDT]]\n** [[Wikidata:WikiProject Ontology/Ontology Course/Projects/SubclassPathTracing|SubclassPathTracing]]\n** [[Wikidata:WikiProject Ontology/Ontology Course/Projects/RoboData|RoboData]]\n** [[Wikidata:WikiProject Ontology/Ontology Course/Projects/institutions|Institutions]]\n** [[Wikidata:WikiProject_Ontology/Ontology_Course/Modeling_time|Modeling time]]\n** [[Wikidata:WikiProject_Ontology/Ontology_Course/Projects/CreatingShapeConstraints|Creating Shape Constraints]]\n\n== Interesting Subpages ==\n\n; [[Wikidata:WikiProject Ontology/Modelling|Modelling with classes in Wikidata]] : A discussion of how classes work in the Wikidata ontology\n\n; [[Wikidata:WikiProject Ontology/Metaclasses|Best Practices for Metaclasses in Wikidata]] : Suggestions on how to set up metaclasses\n\n; [[Wikidata:WikiProject Ontology/Classes|Classes]] : Summary of information on classes\n\n; [[Wikidata:WikiProject Ontology/Problems|Ontology Problems]] : A description of some of the problems in the Wikidata ontology.  There are multiple pages under this page with more information about some of the problems.\n\n; [[Wikidata:WikiProject Ontology/Problems|Ontology Problems/instances of instances of physical object]] : Problems relating to instances of instances of {{Q|223557}} and a suggestion to improve the Wikidata constraint system.\n\n; [[Wikidata:WikiProject Ontology/Issues|Issues]] : Overview of the main ontology issues found in Wikidata at a discussion during WikidataCon 2021\n\n; [[Wikidata:WikiProject Ontology/BFO|BFO]] : Wikidata classes corresponding to BFO classes\n\n; [[Wikidata:WikiProject Ontology/Mapping|Mapping to External Ontologies]] : Beginnings of information on how to link the Wikidata Ontology to external ontologies\n\n; [[Wikidata:WikiProject Ontology/Top-level ontology list|Most-general Classes]] : A list of the two most-general levels of classes in the Wikidata ontology\n\nAll Subpages including redirects:\n[[Wikidata:WikiProject_Ontology/Pages]]\n\n== Resources ==\n===Authored by Wikiproject Ontology Participants===\n* {{Cite Q | Q130629352 }}\n===About Wikidata's Ontology===\n* {{Cite Q | Q27037396 }}\n\n==Tools==\n* [https://angryloki.github.io/wikidata-graph-builder Wikidata Graph Builder]: Makes it easy to visualize our ontology.\n* [[Wikidata:Tools/Enhance user interface#Classification.js|Classification.js]] : visualise the parent classes, reports problem on the WikiProject talk page, the classes an item is an instance of, detects loops in the class tree, detects and visualize class disjointedness violations issues.\n* [[User:Lectrician1/metaclass-check.js|metaclass-check.js]] This adds a warning text next to {{P|31}} statements on classes if their values are not metaclasses.\n* [https://w.wiki/8TiA WDQS query] to check if two classes violates a [[Special:MyLanguage/Help:P2738|{{Label|P2738}}]] statement\n\n==See Also==\n* [[Wikidata:Data model]]\n* [[Wikidata:Item classification]]\n* [[Wikidata:Ontology issues prioritization]]\n* [[Help:Basic membership properties]]\n\n== Userbox ==\n* See: [[Wikidata:Userboxes]]\n{{User Ontology}}\n{{-}}\n\n\n\n==Participants==\n{{participants}}\n\n===Inactive participants===\n<small>(More than one year of inactivity)</small>\n* {{u|I9606}}\n* {{u|Emw}}\n* {{u|Ruud Koot}}\n* {{u|Emitraka}}\n* {{u|Lechatpito}}\n* {{u|DavRosen}}\n* {{u|Fractaler}}\n* {{u|Ddelaiglesia}}\n* {{u|Alessandro Piscopo}}\n* {{u|Ptolusque}}\n* {{u|Malore}}\n* {{u|Wurstbruch}}\n* {{u|Ettorerizza}}\n* {{u|Ninokeys}}\n* {{u|Tris T7}}\n* {{u|Linuxo}}\n* {{u|Gq86}}\n* {{u|Meejies}}\n* {{u|Iwan.Aucamp}}\n* {{u|Tfrancart}}\n* {{u|Luis.ramos.pst.ag}}\n* {{u|Sylvain Leroux}}\n* {{u|Mkbergman}}\n* {{u|The-erinaceous-one}}\n* {{u|Cdo256}}\n* {{u|Rehman}}\n\n== Former Logo ==\n[[File:Wikidata-wikiproject-ontology.png|200px|frameless]]\n\n[[Category:WikiProject Ontology]]"

/-- The imported page is hygienic wikitext. -/
theorem wikiProjectOntology_clean : pageCleanB wikiProjectOntology = true := by native_decide

/-- Printing the imported page and reading it back returns the same page. -/
theorem wikiProjectOntology_reparse :
    parsePage (render wikiProjectOntology) = some wikiProjectOntology :=
  parsePage_render wikiProjectOntology_clean

/-- **Every template called on the imported page is documented.** -/
theorem wikiProjectOntology_uses_registered :
    Registry.usesOnlyRegistered wikiProjectOntology = true := by native_decide

/-! ## The generated pages -/

/-- The items of the upper-ontology fragment, with their labels. -/
def upperItems : List IndexItem :=
  UpperOntology.kb.items.map fun q =>
    let id := Cli.qidText q
    (id, glossary.labelOf id)

/-- The heading of the generated upper-ontology index. -/
def upperHeading : String :=
  "This page is generated from the formalized upper ontology.\n\n"

/-- **A generated page**: an index of the upper-ontology fragment. -/
def upperOntologyIndex : Page := sectionPage "Q" upperHeading upperItems

/-- The generated index prints to wikitext that reads back as the same page. -/
theorem upperOntologyIndex_roundTrip :
    parsePage (render upperOntologyIndex) = some upperOntologyIndex :=
  sectionPage_roundTrip "Q" upperHeading (by decide) upperItems (by decide) (by native_decide)

/-- Every template the generated index calls is documented. -/
theorem upperOntologyIndex_uses_registered :
    Registry.usesOnlyRegistered upperOntologyIndex = true := by native_decide

/-- The properties the glossary grounds, with their labels. -/
def propertyItems : List IndexItem :=
  (glossary.entries.filter fun e => e.id.startsWith "P").map fun e => (e.id, e.label)

/-- The heading of the generated property index. -/
def propertyHeading : String :=
  "This page is generated from the glossary of the formalization.\n\n"

/-- **A generated page**: an index of the properties used in the formalization. -/
def propertyIndex : Page := sectionPage "P" propertyHeading propertyItems

/-- The generated property index prints to wikitext that reads back as the same
page. -/
theorem propertyIndex_roundTrip :
    parsePage (render propertyIndex) = some propertyIndex :=
  sectionPage_roundTrip "P" propertyHeading (by decide) propertyItems (by decide)
    (by native_decide)

/-- Every template the generated property index calls is documented. -/
theorem propertyIndex_uses_registered :
    Registry.usesOnlyRegistered propertyIndex = true := by native_decide

/-- The pages this development ships, with the file each is written to. -/
def allPages : List (String × Page) :=
  [("Wikidata_WikiProject_Ontology.wiki", wikiProjectOntology),
   ("Upper_ontology_index.wiki", upperOntologyIndex),
   ("Property_index.wiki", propertyIndex)]

end Pages
end Wiki
end Wikidata
