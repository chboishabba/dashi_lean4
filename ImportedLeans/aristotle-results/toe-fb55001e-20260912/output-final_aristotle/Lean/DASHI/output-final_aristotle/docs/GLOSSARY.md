# The glossary: every Wikidata term of this development

Every Wikidata identifier that occurs anywhere in this project — in the Lean
sources, in the downloaded corpus under `data/`, in the generated modules and
in the documentation — looked up in Wikidata itself.  For each one the table
gives the English label, the English description and the English Wikipedia
article, all as Wikidata records them.

There are **1610** of them: 51 properties and 1559 items,
926 with an English Wikipedia article.

The table is downloaded by `scripts/fetch_glossary.py`, which also writes
`data/glossary.tsv` and the Lean module `RequestProject/Generated/Glossary.lean`.
The Lean side re-checks it: `RequestProject/Grounded.lean` proves that the table
is well formed, that it covers every item of every downloaded fragment, and that
every notion the formalisation defines is grounded in one of these entities.

A few labels come from Wikidata's language-independent `mul` label rather than
its English one, and an identifier written `Qa → Qb` is a redirect to `Qb`.

Identifiers invented for the hand-written illustrations of the library (`Q1`,
`Q2`, `Q3`, `Q4`, `Q6`, `Q7`, `Q8`, `Q9` and `Q999999`) are *not* references to
Wikidata and are deliberately absent.

## Properties

| id | label | description | article |
|---|---|---|---|
| [P17](https://www.wikidata.org/wiki/Property:P17) | country | sovereign state that this subject item is in (not to be used for human beings) |  |
| [P19](https://www.wikidata.org/wiki/Property:P19) | place of birth | most specific known birth location of a person, animal or fictional character |  |
| [P22](https://www.wikidata.org/wiki/Property:P22) | father | male parent of the subject. For stepfather, use "stepparent" (P3448) |  |
| [P25](https://www.wikidata.org/wiki/Property:P25) | mother | female parent of the subject. For stepmother, use "stepparent" (P3448) |  |
| [P26](https://www.wikidata.org/wiki/Property:P26) | spouse | the subject has the object as their spouse (husband, wife, partner, etc.). Use "unmarried partner" (P451) for non-married companions |  |
| [P27](https://www.wikidata.org/wiki/Property:P27) | country of citizenship | the object is a country that recognizes the subject as its citizen |  |
| [P31](https://www.wikidata.org/wiki/Property:P31) | instance of | type to which this subject corresponds/belongs. Different from P279 (subclass of); for example: K2 is an instance of mountain; volcano is a subclass of mountain |  |
| [P36](https://www.wikidata.org/wiki/Property:P36) | capital | seat of government of a country, province, state or other type of administrative territorial entity |  |
| [P40](https://www.wikidata.org/wiki/Property:P40) | child | subject has object as child. Do not use for stepchildren—use "relative" (P1038), qualified with "kinship to subject" (P1039) |  |
| [P105](https://www.wikidata.org/wiki/Property:P105) | taxon rank | level in a taxonomic hierarchy |  |
| [P131](https://www.wikidata.org/wiki/Property:P131) | located in the administrative territorial entity | the item is located on the territory of the following administrative entity. Use P276 for specifying locations that are non-administrative places and for items about events. Use P1382 if the item falls only partially into the administrative entity |  |
| [P143](https://www.wikidata.org/wiki/Property:P143) | imported from Wikimedia project | source of this claim's value; used in references section by bots or humans importing data from Wikimedia projects |  |
| [P155](https://www.wikidata.org/wiki/Property:P155) | follows | immediately prior item in a series of which the subject is a part, preferably use as qualifier of P179 [if the subject has replaced the preceding item, e.g. political offices, use "replaces" (P1365)] |  |
| [P156](https://www.wikidata.org/wiki/Property:P156) | followed by | immediately following item in a series of which the subject is a part, preferably use as qualifier of P179 [if the subject has been replaced, e.g. political offices, use "replaced by" (P1366)] |  |
| [P171](https://www.wikidata.org/wiki/Property:P171) | parent taxon | closest parent taxon of the taxon in question |  |
| [P179](https://www.wikidata.org/wiki/Property:P179) | part of the series | series which contains the subject |  |
| [P214](https://www.wikidata.org/wiki/Property:P214) | VIAF cluster ID | identifier for the Virtual International Authority File database [format: up to 22 digits]; please note: VIAF is a cluster, the ID can include multiple items |  |
| [P225](https://www.wikidata.org/wiki/Property:P225) | taxon name | correct scientific name of a taxon (according to the reference given) |  |
| [P227](https://www.wikidata.org/wiki/Property:P227) | GND ID | identifier from the Gemeinsame Normdatei authority file of names, subjects, and organizations |  |
| [P248](https://www.wikidata.org/wiki/Property:P248) | stated in | to be used in the references field to refer to the information document or database in which a claim is made; for qualifiers use P805; for the type of document in which a claim is made use P3865 |  |
| [P279](https://www.wikidata.org/wiki/Property:P279) | subclass of | this item is a subclass (subset) of that item; ALL instances of this item are instances of that item; different from P31 (instance of), e.g.: volcano is a subclass of mountain; Everest is an instance of mountain |  |
| [P361](https://www.wikidata.org/wiki/Property:P361) | part of | object of which the subject is a part (if this subject is already part of object A which is a part of object B, then please only make the subject part of object A), inverse property of "has part" (P527, see also "has parts of the class" (P2670)) |  |
| [P460](https://www.wikidata.org/wiki/Property:P460) | said to be the same as | this item is said to be the same as that item, though this may be uncertain or disputed |  |
| [P527](https://www.wikidata.org/wiki/Property:P527) | has part(s) | part of this subject; inverse property of "part of" (P361). See also "has parts of the class" (P2670). |  |
| [P569](https://www.wikidata.org/wiki/Property:P569) | date of birth | date on which the subject was born |  |
| [P571](https://www.wikidata.org/wiki/Property:P571) | inception | time when an entity begins to exist; for date of official opening use P1619 |  |
| [P580](https://www.wikidata.org/wiki/Property:P580) | start time | time an entity begins to exist or a statement starts being valid |  |
| [P582](https://www.wikidata.org/wiki/Property:P582) | end time | moment when an entity ceases to exist and a statement stops being entirely valid or no longer be true |  |
| [P585](https://www.wikidata.org/wiki/Property:P585) | point in time | date something took place, existed or a statement was true; for providing time use the "refine date" property (P4241) |  |
| [P854](https://www.wikidata.org/wiki/Property:P854) | reference URL | should be used for Internet URLs as references. Use "Wikimedia import URL" (P4656) for imports from Wikimedia sites |  |
| [P1038](https://www.wikidata.org/wiki/Property:P1038) | relative | family member (qualify with "kinship to subject", P1039; for direct family member please use specific property) |  |
| [P1039](https://www.wikidata.org/wiki/Property:P1039) | kinship to subject | qualifier of "relative" (P1038) to indicate less usual family relationships (ancestor, son-in-law, adoptions, etc); indicate how the qualificator item is related to the main item |  |
| [P1082](https://www.wikidata.org/wiki/Property:P1082) | population | number of people inhabiting the place; number of people of subject |  |
| [P1376](https://www.wikidata.org/wiki/Property:P1376) | capital of | country, state, department, canton or other administrative division of which the municipality is the governmental seat |  |
| [P1545](https://www.wikidata.org/wiki/Property:P1545) | series ordinal | position of an item in its parent series (most frequently a 1-based index), generally to be used as a qualifier (different from "rank" defined as a class, and from "ranking" defined as a property for evaluating a quality) |  |
| [P1628](https://www.wikidata.org/wiki/Property:P1628) | equivalent property | equivalent property in other ontologies (use in statements on properties, use property URI) |  |
| [P1630](https://www.wikidata.org/wiki/Property:P1630) | formatter URL | web page URL; URI template from which “$1” can be automatically replaced with the effective property value on items. If the site goes offline, set it to deprecated rank. If the formatter URL changes, add a new statement with preferred rank |  |
| [P1647](https://www.wikidata.org/wiki/Property:P1647) | subproperty of | all resources related by this property are also related by that property |  |
| [P1696](https://www.wikidata.org/wiki/Property:P1696) | inverse property | links a property to its inverse property (which relates the subject and object in reverse order) |  |
| [P1709](https://www.wikidata.org/wiki/Property:P1709) | equivalent class | equivalent class in other ontologies (use property URI) |  |
| [P1889](https://www.wikidata.org/wiki/Property:P1889) | different from | item that is different from another item, with which it may be confused |  |
| [P1963](https://www.wikidata.org/wiki/Property:P1963) | properties for this type | when this subject is used as object of “instance of”, the following properties normally apply |  |
| [P2241](https://www.wikidata.org/wiki/Property:P2241) | reason for deprecated rank | qualifier to indicate why a particular statement should have deprecated rank |  |
| [P2370](https://www.wikidata.org/wiki/Property:P2370) | փոխարկում ՄՀ միավորների | conversion of the unit into a coherent SI unit |  |
| [P2670](https://www.wikidata.org/wiki/Property:P2670) | has part(s) of the class | the subject has one or more parts of the object class |  |
| [P2737](https://www.wikidata.org/wiki/Property:P2737) | union of | every instance of this class is an instance of at least one class in that list of classes. Use "list item" P11260 as qualifiers to specify the list of classes |  |
| [P2738](https://www.wikidata.org/wiki/Property:P2738) | disjoint union of | every instance of this class is an instance of exactly one class in that list of classes. Use "list item" P11260 as qualifiers to specify the list of classes |  |
| [P3448](https://www.wikidata.org/wiki/Property:P3448) | stepparent | subject has the object as their stepparent |  |
| [P3831](https://www.wikidata.org/wiki/Property:P3831) | object of statement has role | (qualifier) role held by the predicate value (object) of a statement in the context of that statement; for the role of the item the statement appears on (subject), use P2868 |  |
| [P5137](https://www.wikidata.org/wiki/Property:P5137) | item for this sense | concept corresponding to this sense of a lexeme. Use only on lexeme senses; do not use on items or properties |  |
| [P8810](https://www.wikidata.org/wiki/Property:P8810) | parent | parent of the subject. Only use if neither father (P22) nor mother (P25) nor stepparent (P3448) is applicable. |  |

## Items

| id | label | description | article |
|---|---|---|---|
| [Q5](https://www.wikidata.org/wiki/Q5) | human | any single member of Homo sapiens, unique extant species of the genus Homo | [Human](https://en.wikipedia.org/wiki/Human) |
| [Q21](https://www.wikidata.org/wiki/Q21) | England | country in north-west Europe, part of the United Kingdom | [England](https://en.wikipedia.org/wiki/England) |
| [Q30](https://www.wikidata.org/wiki/Q30) | United States | country located primarily in North America | [United States](https://en.wikipedia.org/wiki/United_States) |
| [Q42](https://www.wikidata.org/wiki/Q42) | Douglas Adams | British science fiction writer and humorist (1952–2001) | [Douglas Adams](https://en.wikipedia.org/wiki/Douglas_Adams) |
| [Q46](https://www.wikidata.org/wiki/Q46) | Europe | terrestrial continent located in north-western Eurasia | [Europe](https://en.wikipedia.org/wiki/Europe) |
| [Q64](https://www.wikidata.org/wiki/Q64) | Berlin | federated state, capital and largest city of Germany | [Berlin](https://en.wikipedia.org/wiki/Berlin) |
| [Q68](https://www.wikidata.org/wiki/Q68) | computer | general-purpose device for performing arithmetic or logical operations | [Computer](https://en.wikipedia.org/wiki/Computer) |
| [Q76](https://www.wikidata.org/wiki/Q76) | Barack Obama | 44th President of the United States (2009–2017) | [Barack Obama](https://en.wikipedia.org/wiki/Barack_Obama) |
| [Q84](https://www.wikidata.org/wiki/Q84) | London | capital and largest city of England and the United Kingdom | [London](https://en.wikipedia.org/wiki/London) |
| [Q90](https://www.wikidata.org/wiki/Q90) | Paris | capital and most populous city in France | [Paris](https://en.wikipedia.org/wiki/Paris) |
| [Q140](https://www.wikidata.org/wiki/Q140) | lion | species of big cat | [Lion](https://en.wikipedia.org/wiki/Lion) |
| [Q145](https://www.wikidata.org/wiki/Q145) | United Kingdom | island country in north-west Europe | [United Kingdom](https://en.wikipedia.org/wiki/United_Kingdom) |
| [Q171](https://www.wikidata.org/wiki/Q171) | wiki | type of website that visitors can edit | [Wiki](https://en.wikipedia.org/wiki/Wiki) |
| [Q183](https://www.wikidata.org/wiki/Q183) | Germany | country in Central Europe | [Germany](https://en.wikipedia.org/wiki/Germany) |
| [Q188](https://www.wikidata.org/wiki/Q188) | German | West Germanic language | [German language](https://en.wikipedia.org/wiki/German_language) |
| [Q198](https://www.wikidata.org/wiki/Q198) | war | organized and prolonged violent conflict between different nations, states, or different groups within a nation or state | [War](https://en.wikipedia.org/wiki/War) |
| [Q308](https://www.wikidata.org/wiki/Q308) | Mercury | first planet from the Solar System and smallest among all, tellurian and with extreme temperatures | [Mercury (planet)](https://en.wikipedia.org/wiki/Mercury_%28planet%29) |
| [Q328](https://www.wikidata.org/wiki/Q328) | English Wikipedia | English-language edition of Wikipedia | [English Wikipedia](https://en.wikipedia.org/wiki/English_Wikipedia) |
| [Q336](https://www.wikidata.org/wiki/Q336) | science | systematic endeavor that builds and organizes knowledge, and the set of knowledge produced by this system | [Science](https://en.wikipedia.org/wiki/Science) |
| [Q350](https://www.wikidata.org/wiki/Q350) | Cambridge | city in Cambridgeshire, England | [Cambridge](https://en.wikipedia.org/wiki/Cambridge) |
| [Q395](https://www.wikidata.org/wiki/Q395) | mathematics | field of study | [Mathematics](https://en.wikipedia.org/wiki/Mathematics) |
| [Q446](https://www.wikidata.org/wiki/Q446) | wheel | circular item that rotates about an axial bearing; one of the six simple machines | [Wheel](https://en.wikipedia.org/wiki/Wheel) |
| [Q515](https://www.wikidata.org/wiki/Q515) | city | large human settlement | [City](https://en.wikipedia.org/wiki/City) |
| [Q571](https://www.wikidata.org/wiki/Q571) | book | medium for recording information (words or images) typically on bound pages or more abstractly in electronic or audio form | [Book](https://en.wikipedia.org/wiki/Book) |
| [Q729](https://www.wikidata.org/wiki/Q729) | animal | kingdom of multicellular eukaryotic organisms | [Animal](https://en.wikipedia.org/wiki/Animal) |
| [Q735](https://www.wikidata.org/wiki/Q735) | art | general concept that creates expressive work for its beauty or emotional power (use Q838948 for the resulting work, use Q2018526 for the group of creative disciplines) | [Art](https://en.wikipedia.org/wiki/Art) |
| [Q756](https://www.wikidata.org/wiki/Q756) | plant | living thing in the kingdom of photosynthetic eukaryotes | [Plant](https://en.wikipedia.org/wiki/Plant) |
| [Q762](https://www.wikidata.org/wiki/Q762) | Leonardo da Vinci | Italian Renaissance polymath (1452−1519) | [Leonardo da Vinci](https://en.wikipedia.org/wiki/Leonardo_da_Vinci) |
| [Q901](https://www.wikidata.org/wiki/Q901) | scientist | person who uses scientific methods to study in an area of interest | [Scientist](https://en.wikipedia.org/wiki/Scientist) |
| [Q925](https://www.wikidata.org/wiki/Q925) | mercury | chemical element with symbol Hg and atomic number 80 | [Mercury (element)](https://en.wikipedia.org/wiki/Mercury_%28element%29) |
| [Q937](https://www.wikidata.org/wiki/Q937) | Albert Einstein | German-born theoretical physicist (1879–1955) | [Albert Einstein](https://en.wikipedia.org/wiki/Albert_Einstein) |
| [Q1035](https://www.wikidata.org/wiki/Q1035) | Charles Darwin | English naturalist and biologist (1809–1882) | [Charles Darwin](https://en.wikipedia.org/wiki/Charles_Darwin) |
| [Q1084](https://www.wikidata.org/wiki/Q1084) | noun | word that functions as the name of a specific object or set of objects | [Noun](https://en.wikipedia.org/wiki/Noun) |
| [Q1444](https://www.wikidata.org/wiki/Q1444) | organ | musical keyboard instrument | [Organ (music)](https://en.wikipedia.org/wiki/Organ_%28music%29) |
| [Q1713](https://www.wikidata.org/wiki/Q1713) | citation | reference to a source | [Citation](https://en.wikipedia.org/wiki/Citation) |
| [Q1860](https://www.wikidata.org/wiki/Q1860) | English | West Germanic language | [English language](https://en.wikipedia.org/wiki/English_language) |
| [Q2013](https://www.wikidata.org/wiki/Q2013) | Wikidata | free multilingual online knowledge graph | [Wikidata](https://en.wikipedia.org/wiki/Wikidata) |
| [Q3918](https://www.wikidata.org/wiki/Q3918) | university | an institution of tertiary education and research which awards academic degrees in several academic disciplines | [University](https://en.wikipedia.org/wiki/University) |
| [Q3968](https://www.wikidata.org/wiki/Q3968) | algebra | part of mathematics in which letters and other symbols are used to represent numbers and quantities in formulae and equations | [Algebra](https://en.wikipedia.org/wiki/Algebra) |
| [Q5113](https://www.wikidata.org/wiki/Q5113) | bird | class of vertebrates characterized by wings, a feather-covered body and a beak | [Bird](https://en.wikipedia.org/wiki/Bird) |
| [Q5119](https://www.wikidata.org/wiki/Q5119) | capital city | primary governing city of a top-level (country) or first-level and second-level subdivision (country, state, province, regency, etc) political entity | [Capital city](https://en.wikipedia.org/wiki/Capital_city) |
| [Q5592](https://www.wikidata.org/wiki/Q5592) | Michelangelo | Italian artist and architect (1475-1564) | [Michelangelo](https://en.wikipedia.org/wiki/Michelangelo) |
| [Q5891](https://www.wikidata.org/wiki/Q5891) | philosophy | study of questions concerning being, thought, knowledge, and conduct for which no objective answers have been established, using logical reasoning | [Philosophy](https://en.wikipedia.org/wiki/Philosophy) |
| [Q6256](https://www.wikidata.org/wiki/Q6256) | country | distinct territorial body or political entity | [Country](https://en.wikipedia.org/wiki/Country) |
| [Q6266](https://www.wikidata.org/wiki/Q6266) | nation | community of people who share a common language, culture, ethnicity, descent, or history | [Nation](https://en.wikipedia.org/wiki/Nation) |
| [Q7187](https://www.wikidata.org/wiki/Q7187) | gene | basic physical and functional unit of heredity | [Gene](https://en.wikipedia.org/wiki/Gene) |
| [Q7188](https://www.wikidata.org/wiki/Q7188) | government | system or group of people governing an organized community, often a state. traditionally all three branches, legislature, executive and judiciary. in modern englisch often the executive branch. | [Government](https://en.wikipedia.org/wiki/Government) |
| [Q7207](https://www.wikidata.org/wiki/Q7207) | Elizabeth I of England | Queen of England and Ireland from 1558 to 1603  (1533-1603) | [Elizabeth I](https://en.wikipedia.org/wiki/Elizabeth_I) |
| [Q7211](https://www.wikidata.org/wiki/Q7211) | taxonomy | classification of things or concepts, as well as to the principles underlying such a classification, categorization is based on discrete sets, different from meronymy which is dealing with the classification of parts of a whole | [Taxonomy](https://en.wikipedia.org/wiki/Taxonomy) |
| [Q7239](https://www.wikidata.org/wiki/Q7239) | organism | living being or physical living system composed of organic matter | [Organism](https://en.wikipedia.org/wiki/Organism) |
| [Q7259](https://www.wikidata.org/wiki/Q7259) | Ada Lovelace | English mathematician (1815–1852) | [Ada Lovelace](https://en.wikipedia.org/wiki/Ada_Lovelace) |
| [Q7270](https://www.wikidata.org/wiki/Q7270) | republic | form of government where the head of state is elected | [Republic](https://en.wikipedia.org/wiki/Republic) |
| [Q7275](https://www.wikidata.org/wiki/Q7275) | state | organised community living under a system of government; either a sovereign state, constituent state, or federated state | [State (polity)](https://en.wikipedia.org/wiki/State_%28polity%29) |
| [Q7278](https://www.wikidata.org/wiki/Q7278) | political party | organization that seeks to influence government policy and actions and be elected to directly take part on government or legislation | [Political party](https://en.wikipedia.org/wiki/Political_party) |
| [Q7377](https://www.wikidata.org/wiki/Q7377) | mammal | class of animals, mostly terrestrial tetrapods, some aquatic | [Mammal](https://en.wikipedia.org/wiki/Mammal) |
| [Q7380](https://www.wikidata.org/wiki/Q7380) | primate | order of mammals (scientific name: Primates) | [Primate](https://en.wikipedia.org/wiki/Primate) |
| [Q7397](https://www.wikidata.org/wiki/Q7397) | software | non-tangible executable component of a computer | [Software](https://en.wikipedia.org/wiki/Software) |
| [Q7432](https://www.wikidata.org/wiki/Q7432) | species | one of the basic units of biological classification and a taxonomic rank | [Species](https://en.wikipedia.org/wiki/Species) |
| [Q7560](https://www.wikidata.org/wiki/Q7560) | mother | female parent | [Mother](https://en.wikipedia.org/wiki/Mother) |
| [Q7566](https://www.wikidata.org/wiki/Q7566) | parent | progenitor or caregiver of the offspring in their own species, inverse label for property P40 | [Parent](https://en.wikipedia.org/wiki/Parent) |
| [Q7958](https://www.wikidata.org/wiki/Q7958) | explanation | set of statements constructed to describe reasons why such as for facts | [Explanation](https://en.wikipedia.org/wiki/Explanation) |
| [Q7991](https://www.wikidata.org/wiki/Q7991) | natural science | branch of science about the natural world | [Natural science](https://en.wikipedia.org/wiki/Natural_science) |
| [Q8054](https://www.wikidata.org/wiki/Q8054) | protein | biomolecule or biomolecule complex largely consisting of chains of amino acid residues | [Protein](https://en.wikipedia.org/wiki/Protein) |
| [Q8078](https://www.wikidata.org/wiki/Q8078) | logic | study of correct reasoning | [Logic](https://en.wikipedia.org/wiki/Logic) |
| [Q8171](https://www.wikidata.org/wiki/Q8171) | word | smallest linguistic element that will be said in isolation with semantic or pragmatic content | [Word](https://en.wikipedia.org/wiki/Word) |
| [Q8242](https://www.wikidata.org/wiki/Q8242) | literature | polysemous term referring to a written art form, and the set of all literary works | [Literature](https://en.wikipedia.org/wiki/Literature) |
| [Q8366](https://www.wikidata.org/wiki/Q8366) | algorithm | sequence of instructions to perform a task | [Algorithm](https://en.wikipedia.org/wiki/Algorithm) |
| [Q8386](https://www.wikidata.org/wiki/Q8386) | drug | chemical substance having an effect on the body | [Drug](https://en.wikipedia.org/wiki/Drug) |
| [Q8425](https://www.wikidata.org/wiki/Q8425) | society | a group of individuals involved in persistent social interaction or a large social group sharing the same spatial or social territory, typically subject to the same political authority and dominant cultural expectations | [Society](https://en.wikipedia.org/wiki/Society) |
| [Q8436](https://www.wikidata.org/wiki/Q8436) | family | group of people affiliated by consanguinity, law, affinity, or co-residence | [Family](https://en.wikipedia.org/wiki/Family) |
| [Q8513](https://www.wikidata.org/wiki/Q8513) | database | organized collection of data in computing | [Database](https://en.wikipedia.org/wiki/Database) |
| [Q9081](https://www.wikidata.org/wiki/Q9081) | knowledge | awareness of facts, familiarity with individuals and situations, or practical skill; encompasses descriptive, procedural, and acquaintance knowledge, typically characterized as justified true belief distinct from opinion or guesswork | [Knowledge](https://en.wikipedia.org/wiki/Knowledge) |
| [Q9143](https://www.wikidata.org/wiki/Q9143) | programming language | language for communicating instructions to a machine | [Programming language](https://en.wikipedia.org/wiki/Programming_language) |
| [Q9332](https://www.wikidata.org/wiki/Q9332) | behavior | range of actions by entities, living or not, within a system | [Behavior](https://en.wikipedia.org/wiki/Behavior) |
| [Q9420](https://www.wikidata.org/wiki/Q9420) | thought | mental activity involving an individual's subjective consciousness | [Thought](https://en.wikipedia.org/wiki/Thought) |
| [Q9471](https://www.wikidata.org/wiki/Q9471) | epistemology | branch of philosophy studying the nature and scope of knowledge | [Epistemology](https://en.wikipedia.org/wiki/Epistemology) |
| [Q9492](https://www.wikidata.org/wiki/Q9492) | probability | measure of the expectation that an event will occur or a statement is true | [Probability](https://en.wikipedia.org/wiki/Probability) |
| [Q10915](https://www.wikidata.org/wiki/Q10915) | Chordata | phylum of animals | [Chordate](https://en.wikipedia.org/wiki/Chordate) |
| [Q11016](https://www.wikidata.org/wiki/Q11016) | technology | making, modification, usage, and knowledge of tools, machines, techniques, crafts, systems, and methods of organization, or tools and techniques so created | [Technology](https://en.wikipedia.org/wiki/Technology) |
| [Q11019](https://www.wikidata.org/wiki/Q11019) | machine | set of moving and fixed elements that uses energy to perform an intended action | [Machine](https://en.wikipedia.org/wiki/Machine) |
| [Q11028](https://www.wikidata.org/wiki/Q11028) | information | that which informs; the answer to a question; that from which knowledge can be derived | [Information](https://en.wikipedia.org/wiki/Information) |
| [Q11173](https://www.wikidata.org/wiki/Q11173) | chemical compound | pure chemical substance consisting of two or more different chemical elements | [Chemical compound](https://en.wikipedia.org/wiki/Chemical_compound) |
| [Q11184](https://www.wikidata.org/wiki/Q11184) | Julian calendar | calendar introduced by Julius Caesar in 45 BC | [Julian calendar](https://en.wikipedia.org/wiki/Julian_calendar) |
| [Q11344](https://www.wikidata.org/wiki/Q11344) | chemical element | species of atoms having the same number of protons in the atomic nucleus and the same chemical properties, but not necessarily the same mass, or the same stability (or half-lifetime if they are unstable) | [Chemical element](https://en.wikipedia.org/wiki/Chemical_element) |
| [Q11348](https://www.wikidata.org/wiki/Q11348) | function | association of a single output to each input | [Function (mathematics)](https://en.wikipedia.org/wiki/Function_%28mathematics%29) |
| [Q11367](https://www.wikidata.org/wiki/Q11367) | lipid | class of nonpolar substances including those of biological and artificial origin | [Lipid](https://en.wikipedia.org/wiki/Lipid) |
| [Q11369](https://www.wikidata.org/wiki/Q11369) | molecule | smallest possibile amount of a chemical substance | [Molecule](https://en.wikipedia.org/wiki/Molecule) |
| [Q11398](https://www.wikidata.org/wiki/Q11398) | biological classification | method of scientific taxonomy | [Biological classification](https://en.wikipedia.org/wiki/Biological_classification) |
| [Q11424](https://www.wikidata.org/wiki/Q11424) | film | visual art work that simulates experiences and communicates ideas, stories, or emotions through moving images, generally synchronized with sound since the 1930s | [Film](https://en.wikipedia.org/wiki/Film) |
| [Q11442](https://www.wikidata.org/wiki/Q11442) | bicycle | pedal-driven two-wheel vehicle | [Bicycle](https://en.wikipedia.org/wiki/Bicycle) |
| [Q11563](https://www.wikidata.org/wiki/Q11563) | number | mathematical object used to count, label, and measure | [Number](https://en.wikipedia.org/wiki/Number) |
| [Q11567](https://www.wikidata.org/wiki/Q11567) | complex number | number that can be put in the form a + bi, where a and b are real numbers and i is called the imaginary unit | [Complex number](https://en.wikipedia.org/wiki/Complex_number) |
| [Q11573](https://www.wikidata.org/wiki/Q11573) | metre | SI unit of length | [Metre](https://en.wikipedia.org/wiki/Metre) |
| [Q11660](https://www.wikidata.org/wiki/Q11660) | artificial intelligence | field that develops and studies software enabling machines to exhibit intelligent behavior | [Artificial intelligence](https://en.wikipedia.org/wiki/Artificial_intelligence) |
| [Q12132](https://www.wikidata.org/wiki/Q12132) | calendar system | system of organizing days for social, religious, commercial, or administrative purposes | [Calendar](https://en.wikipedia.org/wiki/Calendar) |
| [Q12136](https://www.wikidata.org/wiki/Q12136) | disease | abnormal biological process in an organism driven by a specific pathophysiological mechanism | [Disease](https://en.wikipedia.org/wiki/Disease) |
| [Q12418](https://www.wikidata.org/wiki/Q12418) | Mona Lisa | oil painting by Leonardo da Vinci in the Louvre, Paris | [Mona Lisa](https://en.wikipedia.org/wiki/Mona_Lisa) |
| [Q12503](https://www.wikidata.org/wiki/Q12503) | integer | number that can be written without a fractional or decimal component | [Integer](https://en.wikipedia.org/wiki/Integer) |
| [Q12916](https://www.wikidata.org/wiki/Q12916) | real number | quantity along a continuous line | [Real number](https://en.wikipedia.org/wiki/Real_number) |
| [Q13136](https://www.wikidata.org/wiki/Q13136) | reference work | type of work to which one can refer for confirmed facts | [Reference work](https://en.wikipedia.org/wiki/Reference_work) |
| [Q15284](https://www.wikidata.org/wiki/Q15284) | municipality | administrative division having corporate status and usually powers of self-government or jurisdiction | [Municipality](https://en.wikipedia.org/wiki/Municipality) |
| [Q16521](https://www.wikidata.org/wiki/Q16521) | taxon | group of one or more organism(s), which a taxonomist adjudges to be a unit | [Taxon](https://en.wikipedia.org/wiki/Taxon) |
| [Q16549](https://www.wikidata.org/wiki/Q16549) | Piz Surlej | mountain in the Bernina Range of the Alps | [Piz Surlej](https://en.wikipedia.org/wiki/Piz_Surlej) |
| [Q16957](https://www.wikidata.org/wiki/Q16957) | German Democratic Republic | 1949–1990 country in central Europe, unified into modern Germany | [East Germany](https://en.wikipedia.org/wiki/East_Germany) |
| [Q17737](https://www.wikidata.org/wiki/Q17737) | theory | contemplative and rational type of abstract or generalizing thinking, or the results of such thinking | [Theory](https://en.wikipedia.org/wiki/Theory) |
| [Q18848](https://www.wikidata.org/wiki/Q18848) | module | generalization of vector space, with scalars in a ring instead of a field | [Module (mathematics)](https://en.wikipedia.org/wiki/Module_%28mathematics%29) |
| [Q21198](https://www.wikidata.org/wiki/Q21198) | computer science | study of computation | [Computer science](https://en.wikipedia.org/wiki/Computer_science) |
| [Q22687](https://www.wikidata.org/wiki/Q22687) | bank | financial institution that accepts deposits | [Bank](https://en.wikipedia.org/wiki/Bank) |
| [Q22865](https://www.wikidata.org/wiki/Q22865) | independent city of Germany | city or town in Germany that does not form part of another general-purpose local government entity | [Independent cities of Germany](https://en.wikipedia.org/wiki/Independent_cities_of_Germany) |
| [Q25107](https://www.wikidata.org/wiki/Q25107) | power | ability to influence the behavior of others | [Power (political science)](https://en.wikipedia.org/wiki/Power_%28political_science%29) |
| [Q25169](https://www.wikidata.org/wiki/Q25169) | The Hitchhiker's Guide to the Galaxy | 1979–1992 series of five books by Douglas Adams | [The Hitchhiker's Guide to the Galaxy](https://en.wikipedia.org/wiki/The_Hitchhiker%27s_Guide_to_the_Galaxy) |
| [Q25188](https://www.wikidata.org/wiki/Q25188) | Inception | 2010 film directed by Christopher Nolan | [Inception](https://en.wikipedia.org/wiki/Inception) |
| [Q25241](https://www.wikidata.org/wiki/Q25241) | Vertebrata | a subphylum of Chordata characterized by the presence of a vertebral column, or backbone, which replaces the notochord during development | [Vertebrate](https://en.wikipedia.org/wiki/Vertebrate) |
| [Q25265](https://www.wikidata.org/wiki/Q25265) | Felidae | family of mammals in the order of carnivorans | [Felidae](https://en.wikipedia.org/wiki/Felidae) |
| [Q25306](https://www.wikidata.org/wiki/Q25306) | Carnivora | order of placental mammals | [Carnivora](https://en.wikipedia.org/wiki/Carnivora) |
| [Q25326](https://www.wikidata.org/wiki/Q25326) | Mollusca | phylum of animals | [Mollusca](https://en.wikipedia.org/wiki/Mollusca) |
| [Q27801](https://www.wikidata.org/wiki/Q27801) | non-fiction literature | literary genre | [Nonfiction literature](https://en.wikipedia.org/wiki/Nonfiction_literature) |
| [Q28108](https://www.wikidata.org/wiki/Q28108) | political system | system of politics and government | [Political system](https://en.wikipedia.org/wiki/Political_system) |
| [Q28640](https://www.wikidata.org/wiki/Q28640) | profession | occupation requiring specialized training | [Profession](https://en.wikipedia.org/wiki/Profession) |
| [Q28865](https://www.wikidata.org/wiki/Q28865) | Python | general-purpose programming language | [Python (programming language)](https://en.wikipedia.org/wiki/Python_%28programming_language%29) |
| [Q28877](https://www.wikidata.org/wiki/Q28877) | good/s | tangible or intangible thing, except a service, that satisfies human wants and provides utility | [Goods](https://en.wikipedia.org/wiki/Goods) |
| [Q29485](https://www.wikidata.org/wiki/Q29485) | error | action or proposition which is inaccurate or incorrect, that could result in failure or deviation from the intended performance or behaviour | [Error](https://en.wikipedia.org/wiki/Error) |
| [Q31184](https://www.wikidata.org/wiki/Q31184) | sibling | one of two or more individuals having at least one parent in common | [Sibling](https://en.wikipedia.org/wiki/Sibling) |
| [Q31629](https://www.wikidata.org/wiki/Q31629) | type of sport | specific sport. Do not use with P279 (subclass of) |  |
| [Q34104](https://www.wikidata.org/wiki/Q34104) | science and technology | topic encompassing both science and technology and their interactions | [Science and technology](https://en.wikipedia.org/wiki/Science_and_technology) |
| [Q34740](https://www.wikidata.org/wiki/Q34740) | genus | taxonomic rank used in the biological classification of living and fossil organisms, and viruses | [Genus](https://en.wikipedia.org/wiki/Genus) |
| [Q34770](https://www.wikidata.org/wiki/Q34770) | language | particular system of communication, often named for the region or peoples that use it |  |
| [Q35120](https://www.wikidata.org/wiki/Q35120) | entity | anything that can be considered, discussed, or observed | [Entity](https://en.wikipedia.org/wiki/Entity) |
| [Q35127](https://www.wikidata.org/wiki/Q35127) | website | set of related web pages served from a single web domain | [Website](https://en.wikipedia.org/wiki/Website) |
| [Q35409](https://www.wikidata.org/wiki/Q35409) | family | taxonomic rank (or a taxon at that rank) between order and genus | [Family (taxonomy)](https://en.wikipedia.org/wiki/Family_%28taxonomy%29) |
| [Q35758](https://www.wikidata.org/wiki/Q35758) | matter | substance that has rest mass and volume | [Matter](https://en.wikipedia.org/wiki/Matter) |
| [Q35798](https://www.wikidata.org/wiki/Q35798) | executive branch | branch of the government that has sole authority and responsibility for the administration of the state | [Executive (government)](https://en.wikipedia.org/wiki/Executive_%28government%29) |
| [Q36161](https://www.wikidata.org/wiki/Q36161) | set | well-defined mathematical collection of distinct objects | [Set (mathematics)](https://en.wikipedia.org/wiki/Set_%28mathematics%29) |
| [Q36578](https://www.wikidata.org/wiki/Q36578) | Integrated Authority File | German National Library authority file for personal names, subject headings and corporate bodies | [Integrated Authority File](https://en.wikipedia.org/wiki/Integrated_Authority_File) |
| [Q36602](https://www.wikidata.org/wiki/Q36602) | order | taxonomic rank | [Order (taxonomy)](https://en.wikipedia.org/wiki/Order_%28taxonomy%29) |
| [Q36732](https://www.wikidata.org/wiki/Q36732) | kingdom | taxonomic rank | [Kingdom (taxonomy)](https://en.wikipedia.org/wiki/Kingdom_%28taxonomy%29) |
| [Q36774](https://www.wikidata.org/wiki/Q36774) | web page | single document composed of HTML that is directly viewable via web browsers and accessible via the World Wide Web | [Web page](https://en.wikipedia.org/wiki/Web_page) |
| [Q37517](https://www.wikidata.org/wiki/Q37517) | class | taxonomic rank in biology | [Class (taxonomy)](https://en.wikipedia.org/wiki/Class_%28taxonomy%29) |
| [Q38348](https://www.wikidata.org/wiki/Q38348) | phylum | main taxonomic rank (under the rank kingdom) | [Phylum](https://en.wikipedia.org/wiki/Phylum) |
| [Q38723](https://www.wikidata.org/wiki/Q38723) | higher education institution | institution that provides higher education (e.g., universities, vocational universities, community colleges, liberal arts colleges, institutes of technology, and others) | [Higher education institution](https://en.wikipedia.org/wiki/Higher_education_institution) |
| [Q39072](https://www.wikidata.org/wiki/Q39072) | microeconomics | branch of economics that studies the behavior of individual households and firms in making decisions on the allocation of limited resources | [Microeconomics](https://en.wikipedia.org/wiki/Microeconomics) |
| [Q42106](https://www.wikidata.org/wiki/Q42106) | synonym | word or phrase that means exactly or nearly the same as another word or phrase in the same language | [Synonym](https://en.wikipedia.org/wiki/Synonym) |
| [Q42240](https://www.wikidata.org/wiki/Q42240) | research | systematic study undertaken to increase knowledge | [Research](https://en.wikipedia.org/wiki/Research) |
| [Q42848](https://www.wikidata.org/wiki/Q42848) | data | codified, fixed and transmissible information, that may be arranged for automatic processing | [Data](https://en.wikipedia.org/wiki/Data) |
| [Q42989](https://www.wikidata.org/wiki/Q42989) | topology | branch of mathematics | [Topology](https://en.wikipedia.org/wiki/Topology) |
| [Q43229](https://www.wikidata.org/wiki/Q43229) | organization | social entity established to meet needs or pursue goals | [Organization](https://en.wikipedia.org/wiki/Organization) |
| [Q44946](https://www.wikidata.org/wiki/Q44946) | point | fundamental object of geometry: locus within which we can distinguish no other locus than itself | [Point (geometry)](https://en.wikipedia.org/wiki/Point_%28geometry%29) |
| [Q47574](https://www.wikidata.org/wiki/Q47574) | unit of measurement | real scalar quantity, defined and adopted by convention, with which any other quantity of the same kind can be compared to express the ratio of the two quantities as a number (VIM) | [Unit of measurement](https://en.wikipedia.org/wiki/Unit_of_measurement) |
| [Q49848](https://www.wikidata.org/wiki/Q49848) | document | form for preservation of structured and identified information | [Document](https://en.wikipedia.org/wiki/Document) |
| [Q52948](https://www.wikidata.org/wiki/Q52948) | interaction | kind of action that occurs as two or more objects have an effect upon one another |  |
| [Q54871](https://www.wikidata.org/wiki/Q54871) | SPARQL | RDF query language | [SPARQL](https://en.wikipedia.org/wiki/SPARQL) |
| [Q54872](https://www.wikidata.org/wiki/Q54872) | Resource Description Framework | data model for describing resources on the Web | [Resource Description Framework](https://en.wikipedia.org/wiki/Resource_Description_Framework) |
| [Q56061](https://www.wikidata.org/wiki/Q56061) | administrative territorial entity | territorial entity for administration purposes, with or without its own local government | [Administrative division](https://en.wikipedia.org/wiki/Administrative_division) |
| [Q58778](https://www.wikidata.org/wiki/Q58778) | system | set of interacting or interdependent components | [System](https://en.wikipedia.org/wiki/System) |
| [Q64861](https://www.wikidata.org/wiki/Q64861) | transitive relation | binary relation R with the property that xRy and yRz implies xRz | [Transitive relation](https://en.wikipedia.org/wiki/Transitive_relation) |
| [Q65943](https://www.wikidata.org/wiki/Q65943) | theorem | in mathematics, a statement that has been proved | [Theorem](https://en.wikipedia.org/wiki/Theorem) |
| [Q72638](https://www.wikidata.org/wiki/Q72638) | consumer | organism in an ecological food chain that receives energy by consuming other organisms | [Consumer (food chain)](https://en.wikipedia.org/wiki/Consumer_%28food_chain%29) |
| [Q79188](https://www.wikidata.org/wiki/Q79188) | sedenion | 16-dimensional hypercomplex number | [Sedenion](https://en.wikipedia.org/wiki/Sedenion) |
| [Q79529](https://www.wikidata.org/wiki/Q79529) | chemical substance | matter of constant composition best characterized by the entities (molecules, formula units, atoms) it is composed of and characterized by physical properties like density | [Substance (chemistry)](https://en.wikipedia.org/wiki/Substance_%28chemistry%29) |
| [Q80006](https://www.wikidata.org/wiki/Q80006) | computer programming | the process of designing and building an executable computer program to accomplish a specific computing result or to perform a specific task | [Computer programming](https://en.wikipedia.org/wiki/Computer_programming) |
| [Q81163](https://www.wikidata.org/wiki/Q81163) | polymer | substance composed of macromolecules with repeating structural units | [Polymer](https://en.wikipedia.org/wiki/Polymer) |
| [Q82042](https://www.wikidata.org/wiki/Q82042) | part of speech | category of words based on shared grammatical properties in a clause | [Part of speech](https://en.wikipedia.org/wiki/Part_of_speech) |
| [Q82753](https://www.wikidata.org/wiki/Q82753) | computer file | contained block of information on a computer | [Computer file](https://en.wikipedia.org/wiki/Computer_file) |
| [Q82794](https://www.wikidata.org/wiki/Q82794) | region | 2D or 3D defined space on something, mainly in terrestrial and astrophysics sciences | [Region](https://en.wikipedia.org/wiki/Region) |
| [Q82799](https://www.wikidata.org/wiki/Q82799) | name | word or phrase used for identification | [Name](https://en.wikipedia.org/wiki/Name) |
| [Q83267](https://www.wikidata.org/wiki/Q83267) | crime | unlawful act punishable by an authority | [Crime](https://en.wikipedia.org/wiki/Crime) |
| [Q83478](https://www.wikidata.org/wiki/Q83478) | group | algebraic set with an invertible, associative internal operation admitting a neutral element | [Group (mathematics)](https://en.wikipedia.org/wiki/Group_%28mathematics%29) |
| [Q101072](https://www.wikidata.org/wiki/Q101072) | definition | statement of the meaning of a word or phrase | [Definition](https://en.wikipedia.org/wiki/Definition) |
| [Q104493](https://www.wikidata.org/wiki/Q104493) | risk | potential for uncontrolled loss due to underlying vulnerability or uncertainties | [Risk](https://en.wikipedia.org/wiki/Risk) |
| [Q107390](https://www.wikidata.org/wiki/Q107390) | federated state | territorial and constitutional community forming part of a federal union | [Federated state](https://en.wikipedia.org/wiki/Federated_state) |
| [Q107715](https://www.wikidata.org/wiki/Q107715) | physical quantity | quantitative characterization of an aspect of a physical entity, phenomenon, event, process, transformation, relation, system, or substance | [Physical quantity](https://en.wikipedia.org/wiki/Physical_quantity) |
| [Q108163](https://www.wikidata.org/wiki/Q108163) | proposition | idea that is true or false and may be expressed in a declarative sentence | [Proposition](https://en.wikipedia.org/wiki/Proposition) |
| [Q110786](https://www.wikidata.org/wiki/Q110786) | singular | grammatical number | [Singular (grammatical number)](https://en.wikipedia.org/wiki/Singular_%28grammatical_number%29) |
| [Q120208](https://www.wikidata.org/wiki/Q120208) | emerging technology | Technologies whose development, practical applications, or both are still largely unrealized | [Emerging technologies](https://en.wikipedia.org/wiki/Emerging_technologies) |
| [Q121182](https://www.wikidata.org/wiki/Q121182) | information system | combination of information, resources, activities and people that support tasks in an organization; group of components that interact to produce information | [Information system](https://en.wikipedia.org/wiki/Information_system) |
| [Q121769](https://www.wikidata.org/wiki/Q121769) | reference | relationship between objects in which one object designates, or acts as a means by which to connect to or link to, another object | [Reference](https://en.wikipedia.org/wiki/Reference) |
| [Q123705](https://www.wikidata.org/wiki/Q123705) | neighborhood | geographically localized community within a larger city, town or suburb | [Neighbourhood](https://en.wikipedia.org/wiki/Neighbourhood) |
| [Q124490](https://www.wikidata.org/wiki/Q124490) | violence | destructive action characterized by lack of empathy and involving communication, manipulation, coercion and/or punishment | [Violence](https://en.wikipedia.org/wiki/Violence) |
| [Q125977](https://www.wikidata.org/wiki/Q125977) | vector space | the basic algebraic structure of linear algebra; a module over a field, such that its elements can be added together or scaled by elements of the field | [Vector space](https://en.wikipedia.org/wiki/Vector_space) |
| [Q126818](https://www.wikidata.org/wiki/Q126818) | dimensionless quantity | quantity with no physical dimension | [Dimensionless quantity](https://en.wikipedia.org/wiki/Dimensionless_quantity) |
| [Q127244](https://www.wikidata.org/wiki/Q127244) | Gδ set | countable intersection of open sets | [Gδ set](https://en.wikipedia.org/wiki/G%CE%B4_set) |
| [Q127960](https://www.wikidata.org/wiki/Q127960) | Panthera | genus of mammals | [Panthera](https://en.wikipedia.org/wiki/Panthera) |
| [Q130788](https://www.wikidata.org/wiki/Q130788) | chronology | science of arranging events in order of occurrence | [Chronology](https://en.wikipedia.org/wiki/Chronology) |
| [Q130901](https://www.wikidata.org/wiki/Q130901) | binary relation | set of ordered pairs with first element in A and second element in B | [Binary relation](https://en.wikipedia.org/wiki/Binary_relation) |
| [Q130998](https://www.wikidata.org/wiki/Q130998) | equivalence relation | reflexive, symmetric and transitive relation | [Equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation) |
| [Q131093](https://www.wikidata.org/wiki/Q131093) | content management system | software type | [Content management system](https://en.wikipedia.org/wiki/Content_management_system) |
| [Q131841](https://www.wikidata.org/wiki/Q131841) | idea | mental image or concept | [Idea](https://en.wikipedia.org/wiki/Idea) |
| [Q132364](https://www.wikidata.org/wiki/Q132364) | communication protocol | system for exchanging messages between computing systems | [Communication protocol](https://en.wikipedia.org/wiki/Communication_protocol) |
| [Q133250](https://www.wikidata.org/wiki/Q133250) | sequence | ordered list of the same type of elements (finite or infinite) | [Sequence](https://en.wikipedia.org/wiki/Sequence) |
| [Q133442](https://www.wikidata.org/wiki/Q133442) | city-state | independent or autonomous entity whose territory consists of a city | [City-state](https://en.wikipedia.org/wiki/City-state) |
| [Q140283](https://www.wikidata.org/wiki/Q140283) | essentially surjective functor | functor for which all objects of the codomain are isomorphic to some images | [Essentially surjective functor](https://en.wikipedia.org/wiki/Essentially_surjective_functor) |
| [Q141488](https://www.wikidata.org/wiki/Q141488) | graph | mathematical structure made of vertices connected in pairs by edges | [Graph (discrete mathematics)](https://en.wikipedia.org/wiki/Graph_%28discrete_mathematics%29) |
| [Q146481](https://www.wikidata.org/wiki/Q146481) | domain | taxonomic rank (for "ordinary" organisms thus not viruses) | [Domain (taxonomy)](https://en.wikipedia.org/wiki/Domain_%28taxonomy%29) |
| [Q146786](https://www.wikidata.org/wiki/Q146786) | plural | grammatical number | [Plural](https://en.wikipedia.org/wiki/Plural) |
| [Q150866](https://www.wikidata.org/wiki/Q150866) | deuterostome | superphylum or infrakingdom of bilateral animals | [Deuterostome](https://en.wikipedia.org/wiki/Deuterostome) |
| [Q151885](https://www.wikidata.org/wiki/Q151885) | concept | semantic unit understood in different ways, e.g. as mental representation, ability or abstract object (philosophy) | [Concept](https://en.wikipedia.org/wiki/Concept) |
| [Q152478](https://www.wikidata.org/wiki/Q152478) | sponsor | commercial supporter of an event, activity, or person | [Sponsor (commercial)](https://en.wikipedia.org/wiki/Sponsor_%28commercial%29) |
| [Q154954](https://www.wikidata.org/wiki/Q154954) | natural person | real human being as opposed to a non-human legal person | [Natural person](https://en.wikipedia.org/wiki/Natural_person) |
| [Q155076](https://www.wikidata.org/wiki/Q155076) | juridical person | organization recognized by law as a fictitious person | [Juridical person](https://en.wikipedia.org/wiki/Juridical_person) |
| [Q157509](https://www.wikidata.org/wiki/Q157509) | legal guardian | person who has the legal authority to care for the personal and property interests of another person or comunity | [Legal guardian](https://en.wikipedia.org/wiki/Legal_guardian) |
| [Q159344](https://www.wikidata.org/wiki/Q159344) | heterotroph | organism that ingests or absorbs organic carbon (rather than fix carbon from inorganic sources such as carbon dioxide) in order to be able to produce energy | [Heterotroph](https://en.wikipedia.org/wiki/Heterotroph) |
| [Q161172](https://www.wikidata.org/wiki/Q161172) | ring | algebraic structure that has compatible structures of an abelian group and a monoid, in particular having multiplicative identity | [Ring (mathematics)](https://en.wikipedia.org/wiki/Ring_%28mathematics%29) |
| [Q163359](https://www.wikidata.org/wiki/Q163359) | local administrative unit in the NUTS system | lower level of division in the NUTS system |  |
| [Q164307](https://www.wikidata.org/wiki/Q164307) | binary operation | mathematical operation that combines two elements to produce another element | [Binary operation](https://en.wikipedia.org/wiki/Binary_operation) |
| [Q164509](https://www.wikidata.org/wiki/Q164509) | omnivore | animal capable of consuming a variety of foods, usually including both plants and animals as diet | [Omnivore](https://en.wikipedia.org/wiki/Omnivore) |
| [Q167037](https://www.wikidata.org/wiki/Q167037) | corporation | legal entity incorporated through a legislative or registration process | [Corporation](https://en.wikipedia.org/wiki/Corporation) |
| [Q168817](https://www.wikidata.org/wiki/Q168817) | algebraic number | complex number that is a root of a non-zero polynomial in one variable with rational coefficients | [Algebraic number](https://en.wikipedia.org/wiki/Algebraic_number) |
| [Q169336](https://www.wikidata.org/wiki/Q169336) | mixture | substance formed when two or more constituents are physically combined together | [Mixture](https://en.wikipedia.org/wiki/Mixture) |
| [Q170058](https://www.wikidata.org/wiki/Q170058) | continuous function | function such that the preimage of an open set is open | [Continuous function](https://en.wikipedia.org/wiki/Continuous_function) |
| [Q170584](https://www.wikidata.org/wiki/Q170584) | project | collaborative enterprise, frequently involving research or design, that is carefully planned to achieve a particular aim | [Project](https://en.wikipedia.org/wiki/Project) |
| [Q171283](https://www.wikidata.org/wiki/Q171283) | Homo | genus of mammals | [Homo](https://en.wikipedia.org/wiki/Homo) |
| [Q171318](https://www.wikidata.org/wiki/Q171318) | kinship | human relationship term; web of social relationships that form an important part of the lives of most humans in most societies; form of social connection | [Kinship](https://en.wikipedia.org/wiki/Kinship) |
| [Q172847](https://www.wikidata.org/wiki/Q172847) | peptide | natural biological or artificially manufactured short chains of amino acid monomers linked by peptide (amide) bonds | [Peptide](https://en.wikipedia.org/wiki/Peptide) |
| [Q173853](https://www.wikidata.org/wiki/Q173853) | quaternion | noncommutative extension of the real numbers | [Quaternion](https://en.wikipedia.org/wiki/Quaternion) |
| [Q174211](https://www.wikidata.org/wiki/Q174211) | organic compound | chemical compound that contains carbon atoms (with a few exceptions traditionally classified as inorganic compounds) | [Organic compound](https://en.wikipedia.org/wiki/Organic_compound) |
| [Q174728](https://www.wikidata.org/wiki/Q174728) | centimetre | SI unit of length equal to one hundredth of a metre | [Centimetre](https://en.wikipedia.org/wiki/Centimetre) |
| [Q174844](https://www.wikidata.org/wiki/Q174844) | megacity | very large city with a total population in excess of ten million people | [Megacity](https://en.wikipedia.org/wiki/Megacity) |
| [Q175263](https://www.wikidata.org/wiki/Q175263) | data structure | particular way of storing and organizing data in a computer | [Data structure](https://en.wikipedia.org/wiki/Data_structure) |
| [Q177634](https://www.wikidata.org/wiki/Q177634) | community | social unit of human organisms who share common values | [Community](https://en.wikipedia.org/wiki/Community) |
| [Q177646](https://www.wikidata.org/wiki/Q177646) | subset | set whose elements are all contained in another set | [Subset](https://en.wikipedia.org/wiki/Subset) |
| [Q178593](https://www.wikidata.org/wiki/Q178593) | macromolecule | molecule of high relative molecular mass, the structure of which essentially comprises the multiple repetition of units derived, actually or conceptually, from molecules of low relative molecular mass | [Macromolecule](https://en.wikipedia.org/wiki/Macromolecule) |
| [Q178706](https://www.wikidata.org/wiki/Q178706) | institution | structure or mechanism of social order and cooperation governing the behaviour of a set of individuals within a given community | [Institution](https://en.wikipedia.org/wiki/Institution) |
| [Q179700](https://www.wikidata.org/wiki/Q179700) | statue | sculpture primarily conceived as a representational figure | [Statue](https://en.wikipedia.org/wiki/Statue) |
| [Q179899](https://www.wikidata.org/wiki/Q179899) | topological space | set of points and set of neighborhoods that satisfy axioms relating those points to those neighborhoods | [Topological space](https://en.wikipedia.org/wiki/Topological_space) |
| [Q180160](https://www.wikidata.org/wiki/Q180160) | metadata | data about data | [Metadata](https://en.wikipedia.org/wiki/Metadata) |
| [Q180684](https://www.wikidata.org/wiki/Q180684) | conflict | a situation in which unacceptable differences in interests, expectations, values, or opinions occur between individuals, or between or in groups | [Conflict (process)](https://en.wikipedia.org/wiki/Conflict_%28process%29) |
| [Q180907](https://www.wikidata.org/wiki/Q180907) | bijection | mathematical function which is a one-to-one mapping of sets | [Bijection](https://en.wikipedia.org/wiki/Bijection) |
| [Q181175](https://www.wikidata.org/wiki/Q181175) | scalar quantity | quantity represented by a scalar: quantity having no direction | [Scalar (physics)](https://en.wikipedia.org/wiki/Scalar_%28physics%29) |
| [Q182003](https://www.wikidata.org/wiki/Q182003) | injection | mathematical function that preserves distinctness | [Injective function](https://en.wikipedia.org/wiki/Injective_function) |
| [Q183039](https://www.wikidata.org/wiki/Q183039) | form of state | form which a state takes, such as monarchy or republic | [Form of state](https://en.wikipedia.org/wiki/Form_of_state) |
| [Q183366](https://www.wikidata.org/wiki/Q183366) | territory | area of land under a certain jurisdiction | [Territory](https://en.wikipedia.org/wiki/Territory) |
| [Q185148](https://www.wikidata.org/wiki/Q185148) | interval | subset an ordered set that consists of all elements between two given endpoints | [Interval (mathematics)](https://en.wikipedia.org/wiki/Interval_%28mathematics%29) |
| [Q185359](https://www.wikidata.org/wiki/Q185359) | union | operation denoted by symbol “∪” applied on two sets; the set of all distinct elements in the collection | [Union (set theory)](https://en.wikipedia.org/wiki/Union_%28set_theory%29) |
| [Q185698](https://www.wikidata.org/wiki/Q185698) | methodology | system of methods, principles, and rules used in a particular discipline or investigative procedure | [Methodology](https://en.wikipedia.org/wiki/Methodology) |
| [Q185837](https://www.wikidata.org/wiki/Q185837) | intersection | concept in set theory (for the term in geometry, see Q1364910) | [Intersection (set theory)](https://en.wikipedia.org/wiki/Intersection_%28set_theory%29) |
| [Q186081](https://www.wikidata.org/wiki/Q186081) | time interval | temporal extent having a beginning, an end and a duration |  |
| [Q186408](https://www.wikidata.org/wiki/Q186408) | point in time | position of a particular instant in time |  |
| [Q187432](https://www.wikidata.org/wiki/Q187432) | scripting language | programming language for run-time events | [Scripting language](https://en.wikipedia.org/wiki/Scripting_language) |
| [Q187931](https://www.wikidata.org/wiki/Q187931) | phrase | sequence of at least two words | [Phrase](https://en.wikipedia.org/wiki/Phrase) |
| [Q188619](https://www.wikidata.org/wiki/Q188619) | hierarchy | system of elements with multiple levels or tiers that are subordinated to each other | [Hierarchy](https://en.wikipedia.org/wiki/Hierarchy) |
| [Q188777](https://www.wikidata.org/wiki/Q188777) | amides | any derivative of an oxoacid in which a (possibly substituted) amino group replaces an acidic hydroxy group | [Amide](https://en.wikipedia.org/wiki/Amide) |
| [Q188889](https://www.wikidata.org/wiki/Q188889) | code | method to represent information for various purposes (storage, transmission, protection against unauthorized access etc.) | [Code](https://en.wikipedia.org/wiki/Code) |
| [Q189112](https://www.wikidata.org/wiki/Q189112) | isomorphism | in mathematics, invertible morphism | [Isomorphism](https://en.wikipedia.org/wiki/Isomorphism) |
| [Q190087](https://www.wikidata.org/wiki/Q190087) | data type | classification of data in computer science | [Data type](https://en.wikipedia.org/wiki/Data_type) |
| [Q190109](https://www.wikidata.org/wiki/Q190109) | field | commutative ring in which every nonzero element is inversible | [Field (mathematics)](https://en.wikipedia.org/wiki/Field_%28mathematics%29) |
| [Q191067](https://www.wikidata.org/wiki/Q191067) | article | written work forming an independent part of a publication such as a journal, newspaper, or magazine | [Article (publishing)](https://en.wikipedia.org/wiki/Article_%28publishing%29) |
| [Q191290](https://www.wikidata.org/wiki/Q191290) | ordered pair | pair of mathematical objects; tuple of specific length (tuple length n=2) | [Ordered pair](https://en.wikipedia.org/wiki/Ordered_pair) |
| [Q191797](https://www.wikidata.org/wiki/Q191797) | aggression | social interaction aiming at inflicting harm or unpleasantness | [Aggression](https://en.wikipedia.org/wiki/Aggression) |
| [Q192161](https://www.wikidata.org/wiki/Q192161) | formal language | set of strings of symbols that may be constrained by rules that are specific to it; words whose letters are taken from an alphabet and are well-formed according to a specific set of rules | [Formal language](https://en.wikipedia.org/wiki/Formal_language) |
| [Q192276](https://www.wikidata.org/wiki/Q192276) | measure | function assigning numbers to some subsets of a set, which could be seen as a generalization of length, area, volume and integral | [Measure (mathematics)](https://en.wikipedia.org/wiki/Measure_%28mathematics%29) |
| [Q192498](https://www.wikidata.org/wiki/Q192498) | administrative territorial entity of France | class grouping all types of territorial divisions of France (administrative or electoral) | [Administrative divisions of France](https://en.wikipedia.org/wiki/Administrative_divisions_of_France) |
| [Q192611](https://www.wikidata.org/wiki/Q192611) | electoral unit | territorial division made or used for elections | [Electoral district](https://en.wikipedia.org/wiki/Electoral_district) |
| [Q194404](https://www.wikidata.org/wiki/Q194404) | monotonic function | function between ordered sets that preserves or reverses the given order | [Monotonic function](https://en.wikipedia.org/wiki/Monotonic_function) |
| [Q194980](https://www.wikidata.org/wiki/Q194980) | intangible good | good that does not have a physical nature and can be separated from its creator's labor | [Intangible good](https://en.wikipedia.org/wiki/Intangible_good) |
| [Q200250](https://www.wikidata.org/wiki/Q200250) | metropolis | large and significant city or urban area usually with millions of inhabitants | [Metropolis](https://en.wikipedia.org/wiki/Metropolis) |
| [Q202906](https://www.wikidata.org/wiki/Q202906) | homeomorphism | isomorphism between topological spaces; continuous bijection with continuous inverse | [Homeomorphism](https://en.wikipedia.org/wiki/Homeomorphism) |
| [Q203066](https://www.wikidata.org/wiki/Q203066) | relation | property that assigns truth values to k-tuples of individuals | [Finitary relation](https://en.wikipedia.org/wiki/Finitary_relation) |
| [Q205464](https://www.wikidata.org/wiki/Q205464) | algebraic structure | set equipped with one or more finitary operations defined on it | [Algebraic structure](https://en.wikipedia.org/wiki/Algebraic_structure) |
| [Q205961](https://www.wikidata.org/wiki/Q205961) | skill | learned ability and competence to carry out an action | [Skill](https://en.wikipedia.org/wiki/Skill) |
| [Q206229](https://www.wikidata.org/wiki/Q206229) | biomolecule | molecule that is produced by a living organism | [Biomolecule](https://en.wikipedia.org/wiki/Biomolecule) |
| [Q207348](https://www.wikidata.org/wiki/Q207348) | semigroup | algebraic structure with an associative binary operation | [Semigroup](https://en.wikipedia.org/wiki/Semigroup) |
| [Q207643](https://www.wikidata.org/wiki/Q207643) | linear map | mapping that preserves the operations of addition and scalar multiplication | [Linear map](https://en.wikipedia.org/wiki/Linear_map) |
| [Q208237](https://www.wikidata.org/wiki/Q208237) | monoid | algebraic structure with an associative operation and an identity element | [Monoid](https://en.wikipedia.org/wiki/Monoid) |
| [Q208511](https://www.wikidata.org/wiki/Q208511) | global city | city which is an important node in the global economy | [Global city](https://en.wikipedia.org/wiki/Global_city) |
| [Q210953](https://www.wikidata.org/wiki/Q210953) | solar calendar | type of calendar | [Solar calendar](https://en.wikipedia.org/wiki/Solar_calendar) |
| [Q211496](https://www.wikidata.org/wiki/Q211496) | high-level programming language | programming language with strong abstraction from details of hardware | [High-level programming language](https://en.wikipedia.org/wiki/High-level_programming_language) |
| [Q211548](https://www.wikidata.org/wiki/Q211548) | locus | set of points whose location satisfies or is determined by one or more specified conditions | [Locus (mathematics)](https://en.wikipedia.org/wiki/Locus_%28mathematics%29) |
| [Q211606](https://www.wikidata.org/wiki/Q211606) | social structure | aggregate of patterned social arrangements in society | [Social structure](https://en.wikipedia.org/wiki/Social_structure) |
| [Q211790](https://www.wikidata.org/wiki/Q211790) | logical operator | symbol or word which can be applied to statements (of either a formal or a natural language) to produce a new statement | [Logical connective](https://en.wikipedia.org/wiki/Logical_connective) |
| [Q212434](https://www.wikidata.org/wiki/Q212434) | Olympic sport | type of sport with events contested at the Olympic Games | [Olympic sports](https://en.wikipedia.org/wiki/Olympic_sports) |
| [Q213051](https://www.wikidata.org/wiki/Q213051) | non-fiction | type of works in contrast to fictional ones | [Non-fiction](https://en.wikipedia.org/wiki/Non-fiction) |
| [Q213363](https://www.wikidata.org/wiki/Q213363) | open set | set that does not contain any of its boundary points | [Open set](https://en.wikipedia.org/wiki/Open_set) |
| [Q214339](https://www.wikidata.org/wiki/Q214339) | role | set of behaviours, rights, obligations, beliefs, and norms expected from an individual that has a certain social status | [Role](https://en.wikipedia.org/wiki/Role) |
| [Q214609](https://www.wikidata.org/wiki/Q214609) | material | substance that can occur in different amounts, all with some similar [mixture of some] characteristics, and with which objects can be made | [Material](https://en.wikipedia.org/wiki/Material) |
| [Q215111](https://www.wikidata.org/wiki/Q215111) | homomorphism | structure-preserving map between two (algebraic, relational or mixed) structures of the same signature | [Homomorphism](https://en.wikipedia.org/wiki/Homomorphism) |
| [Q215382](https://www.wikidata.org/wiki/Q215382) | disjoint sets | sets with no element in common | [Disjoint sets](https://en.wikipedia.org/wiki/Disjoint_sets) |
| [Q215627](https://www.wikidata.org/wiki/Q215627) | person | being that has certain capacities or attributes constituting personhood (for humans, use Q5 [human] with P31 [instance of]) | [Person](https://en.wikipedia.org/wiki/Person) |
| [Q216353](https://www.wikidata.org/wiki/Q216353) | title | qualified name, rank, or other indication of a class or role given to or inherited by a person, often affixed to a person's name | [Title](https://en.wikipedia.org/wiki/Title) |
| [Q217413](https://www.wikidata.org/wiki/Q217413) | category theory | branch of mathematics studying categories, functors, and natural transformations | [Category theory](https://en.wikipedia.org/wiki/Category_theory) |
| [Q217594](https://www.wikidata.org/wiki/Q217594) | class | mathematical collection of sets that can be defined based on a property of its members (set theory) | [Class (set theory)](https://en.wikipedia.org/wiki/Class_%28set_theory%29) |
| [Q217602](https://www.wikidata.org/wiki/Q217602) | analysis | process of applying analytical methods to existing data of a specific type, breaking a complex topic or substance into smaller parts in order to gain a better understanding of it | [Analysis](https://en.wikipedia.org/wiki/Analysis) |
| [Q217608](https://www.wikidata.org/wiki/Q217608) | fixed point | point that is left unchanged by a function | [Fixed point (mathematics)](https://en.wikipedia.org/wiki/Fixed_point_%28mathematics%29) |
| [Q221173](https://www.wikidata.org/wiki/Q221173) | outline of academic disciplines | overviews of and topical guides to academic disciplines | [Outline of academic disciplines](https://en.wikipedia.org/wiki/Outline_of_academic_disciplines) |
| [Q223393](https://www.wikidata.org/wiki/Q223393) | literary genre | category of literary composition | [Literary genre](https://en.wikipedia.org/wiki/Literary_genre) |
| [Q223557](https://www.wikidata.org/wiki/Q223557) | physical object | singular aggregation of tangible substance(s) such as matter or radiation, with overall properties;thing subject to physical interactions | [Physical object](https://en.wikipedia.org/wiki/Physical_object) |
| [Q223642](https://www.wikidata.org/wiki/Q223642) | interpersonal relationship | strong, deep, or close association or acquaintance between two or more people | [Interpersonal relationship](https://en.wikipedia.org/wiki/Interpersonal_relationship) |
| [Q223973](https://www.wikidata.org/wiki/Q223973) | godparent | person who sponsors a child's baptism | [Godparent](https://en.wikipedia.org/wiki/Godparent) |
| [Q229102](https://www.wikidata.org/wiki/Q229102) | surjective function | function such that every element of the codomain has a preimage | [Surjective function](https://en.wikipedia.org/wiki/Surjective_function) |
| [Q230855](https://www.wikidata.org/wiki/Q230855) | physical state | describes the current properties of a physical system |  |
| [Q230883](https://www.wikidata.org/wiki/Q230883) | quantum state | state of an isolated quantum system, represented as an element of a projective Hilbert space | [Quantum state](https://en.wikipedia.org/wiki/Quantum_state) |
| [Q234460](https://www.wikidata.org/wiki/Q234460) | text | object that can be "read" by reader; result of writing | [Text (literary theory)](https://en.wikipedia.org/wiki/Text_%28literary_theory%29) |
| [Q235557](https://www.wikidata.org/wiki/Q235557) | file format | formalized structure of information stored in a storage medium | [File format](https://en.wikipedia.org/wiki/File_format) |
| [Q241317](https://www.wikidata.org/wiki/Q241317) | computing platform | environment in which a piece of software is executed | [Computing platform](https://en.wikipedia.org/wiki/Computing_platform) |
| [Q244793](https://www.wikidata.org/wiki/Q244793) | twin cities | two cities or urban centres that are founded in close geographic proximity and then grow into each other over time | [Twin cities](https://en.wikipedia.org/wiki/Twin_cities) |
| [Q246672](https://www.wikidata.org/wiki/Q246672) | mathematical object | object or value related to or describable using mathematical concepts or properties | [Mathematical object](https://en.wikipedia.org/wiki/Mathematical_object) |
| [Q254347](https://www.wikidata.org/wiki/Q254347) | Dedekind domain | ring with unique factorization for ideals (mathematics) | [Dedekind domain](https://en.wikipedia.org/wiki/Dedekind_domain) |
| [Q257391](https://www.wikidata.org/wiki/Q257391) | federal capital | national capital city in a federal state | [Federal capital](https://en.wikipedia.org/wiki/Federal_capital) |
| [Q259590](https://www.wikidata.org/wiki/Q259590) | flexible algebra | algebra whose internal binary operation over its base set is associative and commutative at least for any triplet of the same base set whose first and last of the three items are equal | [Flexible algebra](https://en.wikipedia.org/wiki/Flexible_algebra) |
| [Q262166](https://www.wikidata.org/wiki/Q262166) | municipality in Germany | lowest official level of territorial division in Germany | [Municipalities of Germany](https://en.wikipedia.org/wiki/Municipalities_of_Germany) |
| [Q268592](https://www.wikidata.org/wiki/Q268592) | industry | group of firms that produce a closely related set of raw materials, goods, or services | [Industry (economics)](https://en.wikipedia.org/wiki/Industry_%28economics%29) |
| [Q271669](https://www.wikidata.org/wiki/Q271669) | landform | natural or anthropogenic land feature on the solid surface of the Earth or other planetary body; geomorphological unit in the Earth sciences | [Landform](https://en.wikipedia.org/wiki/Landform) |
| [Q272404](https://www.wikidata.org/wiki/Q272404) | finite set | set that has a finite number of elements | [Finite set](https://en.wikipedia.org/wiki/Finite_set) |
| [Q277759](https://www.wikidata.org/wiki/Q277759) | book series | sequence of books having certain characteristics in common that are formally identified together as a group | [Book series](https://en.wikipedia.org/wiki/Book_series) |
| [Q286583](https://www.wikidata.org/wiki/Q286583) | manifestation | physical or digital embodiment of an information artifact |  |
| [Q288465](https://www.wikidata.org/wiki/Q288465) | group action | operation of the elements of a group as transformations or automorphisms (mathematics) | [Group action](https://en.wikipedia.org/wiki/Group_action) |
| [Q291430](https://www.wikidata.org/wiki/Q291430) | σ-finite measure | mathematical measure | [Σ-finite measure](https://en.wikipedia.org/wiki/%CE%A3-finite_measure) |
| [Q309314](https://www.wikidata.org/wiki/Q309314) | quantity | property that exists in a range of magnitudes or multitudes; property that can exist as a magnitude or multitude | [Quantity](https://en.wikipedia.org/wiki/Quantity) |
| [Q311627](https://www.wikidata.org/wiki/Q311627) | p-adic number | number system for a prime p which extends the ordinary arithmetic of the rational numbers in a different way from the extension of the rational number system to the real and complex number systems | [P-adic number](https://en.wikipedia.org/wiki/P-adic_number) |
| [Q317623](https://www.wikidata.org/wiki/Q317623) | technical standard | required norm or standard established to make it easier to do something in a consistent way | [Technical standard](https://en.wikipedia.org/wiki/Technical_standard) |
| [Q320577](https://www.wikidata.org/wiki/Q320577) | Yoneda lemma | in category theory, a theorem that embeds a locally small category into a category of functors | [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) |
| [Q324254](https://www.wikidata.org/wiki/Q324254) | ontology | specification of a conceptualization | [Ontology (information science)](https://en.wikipedia.org/wiki/Ontology_%28information_science%29) |
| [Q327055](https://www.wikidata.org/wiki/Q327055) | worker | person who works | [Worker](https://en.wikipedia.org/wiki/Worker) |
| [Q327333](https://www.wikidata.org/wiki/Q327333) | government agency | organisational part of a government responsible for specific public services, such as health, judiciary, education, transportation, foreign affairs, etc | [Government agency](https://en.wikipedia.org/wiki/Government_agency) |
| [Q334265](https://www.wikidata.org/wiki/Q334265) | transmission medium | conduit for signal propagation | [Transmission medium](https://en.wikipedia.org/wiki/Transmission_medium) |
| [Q337060](https://www.wikidata.org/wiki/Q337060) | perceptible physical object | entity that is physically perceptible |  |
| [Q338021](https://www.wikidata.org/wiki/Q338021) | well-founded relation | type of binary relation | [Well-founded relation](https://en.wikipedia.org/wiki/Well-founded_relation) |
| [Q340169](https://www.wikidata.org/wiki/Q340169) | communications media | storage and delivery agent of information or data | [Media (communication)](https://en.wikipedia.org/wiki/Media_%28communication%29) |
| [Q350604](https://www.wikidata.org/wiki/Q350604) | armed conflict | conflict including violence where at least one of the acting groups is a state | [Kinetic warfare](https://en.wikipedia.org/wiki/Kinetic_warfare) |
| [Q355020](https://www.wikidata.org/wiki/Q355020) | probability measure | measure of total value one, generalizing probability distributions | [Probability measure](https://en.wikipedia.org/wiki/Probability_measure) |
| [Q355679](https://www.wikidata.org/wiki/Q355679) | carboxamides | class of chemical compounds: amides of carboxylic acids | [Carboxamide](https://en.wikipedia.org/wiki/Carboxamide) |
| [Q357858](https://www.wikidata.org/wiki/Q357858) | adjoint functor | relationship that two functors may have | [Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors) |
| [Q367293](https://www.wikidata.org/wiki/Q367293) | convention | set of agreed, stipulated, or generally accepted standards | [Convention (norm)](https://en.wikipedia.org/wiki/Convention_%28norm%29) |
| [Q368988](https://www.wikidata.org/wiki/Q368988) | idempotence | property of certain operations in mathematics and computer science, that can be applied multiple times without changing the result beyond the initial application | [Idempotence](https://en.wikipedia.org/wiki/Idempotence) |
| [Q370502](https://www.wikidata.org/wiki/Q370502) | mapping | function, sometimes assumed structure-preserving in a proper sense | [Map (mathematics)](https://en.wikipedia.org/wiki/Map_%28mathematics%29) |
| [Q374182](https://www.wikidata.org/wiki/Q374182) | logical consequence | fundamental concept in logic | [Logical consequence](https://en.wikipedia.org/wiki/Logical_consequence) |
| [Q378078](https://www.wikidata.org/wiki/Q378078) | substance | basic ontological concept | [Substance theory](https://en.wikipedia.org/wiki/Substance_theory) |
| [Q379825](https://www.wikidata.org/wiki/Q379825) | element | any one of the distinct objects that make up a set in set theory | [Element of a set](https://en.wikipedia.org/wiki/Element_of_a_set) |
| [Q381060](https://www.wikidata.org/wiki/Q381060) | partition of a set | mathematical ways to group elements of a set | [Partition of a set](https://en.wikipedia.org/wiki/Partition_of_a_set) |
| [Q386597](https://www.wikidata.org/wiki/Q386597) | prime ring | abstract algebra concept | [Prime ring](https://en.wikipedia.org/wiki/Prime_ring) |
| [Q386724](https://www.wikidata.org/wiki/Q386724) | work | intellectual or artistic creation |  |
| [Q387196](https://www.wikidata.org/wiki/Q387196) | description logic | family of formal knowledge representation languages | [Description logic](https://en.wikipedia.org/wiki/Description_logic) |
| [Q387917](https://www.wikidata.org/wiki/Q387917) | administrative divisions of Germany | entities in the administrative structure of Germany | [Administrative divisions of Germany](https://en.wikipedia.org/wiki/Administrative_divisions_of_Germany) |
| [Q402152](https://www.wikidata.org/wiki/Q402152) | ancestor | person from whom another person is descended | [Ancestor](https://en.wikipedia.org/wiki/Ancestor) |
| [Q406957](https://www.wikidata.org/wiki/Q406957) | NUTS 1 statistical territorial entity | first-level administrative regions in NUTS classification | [First-level NUTS of the European Union](https://en.wikipedia.org/wiki/First-level_NUTS_of_the_European_Union) |
| [Q409205](https://www.wikidata.org/wiki/Q409205) | xenobiotic | foreign chemical substance found within an organism or a substance which would not normally be found in a given environment, such as a toxic chemical which is entirely artificial | [Xenobiotic](https://en.wikipedia.org/wiki/Xenobiotic) |
| [Q420330](https://www.wikidata.org/wiki/Q420330) | persistent identifier | long-lasting digital name | [Persistent identifier](https://en.wikipedia.org/wiki/Persistent_identifier) |
| [Q422649](https://www.wikidata.org/wiki/Q422649) | biopolymer | polymer produced by a living organism | [Biopolymer](https://en.wikipedia.org/wiki/Biopolymer) |
| [Q424583](https://www.wikidata.org/wiki/Q424583) | Internationalized Resource Identifier | identifier for resources made using Unicode/ISO 10646 characters specified by RFC 3987 | [Internationalized Resource Identifier](https://en.wikipedia.org/wiki/Internationalized_Resource_Identifier) |
| [Q424689](https://www.wikidata.org/wiki/Q424689) | gene product | biochemical material resulting from expression of a gene | [Gene product](https://en.wikipedia.org/wiki/Gene_product) |
| [Q427626](https://www.wikidata.org/wiki/Q427626) | taxonomic rank | in biology, level in a taxonomic hierarchy | [Taxonomic rank](https://en.wikipedia.org/wiki/Taxonomic_rank) |
| [Q430001](https://www.wikidata.org/wiki/Q430001) | decidability | property of theories that have computable membership | [Decidability (logic)](https://en.wikipedia.org/wiki/Decidability_%28logic%29) |
| [Q451967](https://www.wikidata.org/wiki/Q451967) | intentional human activity | human activity driven by purposeful motives |  |
| [Q466109](https://www.wikidata.org/wiki/Q466109) | subgroup | subset of a mathematical group that forms a group itself | [Subgroup](https://en.wikipedia.org/wiki/Subgroup) |
| [Q467606](https://www.wikidata.org/wiki/Q467606) | model theory | study of classes of mathematical structures from the perspective of mathematical logic | [Model theory](https://en.wikipedia.org/wiki/Model_theory) |
| [Q468756](https://www.wikidata.org/wiki/Q468756) | shore | fringe of land at the edge of a large body of water | [Shore](https://en.wikipedia.org/wiki/Shore) |
| [Q472971](https://www.wikidata.org/wiki/Q472971) | space | mathematical structure of geometric nature | [Space (mathematics)](https://en.wikipedia.org/wiki/Space_%28mathematics%29) |
| [Q474715](https://www.wikidata.org/wiki/Q474715) | partially ordered set | set ordered by a transitive, antisymmetric, and reflexive binary relation | [Partially ordered set](https://en.wikipedia.org/wiki/Partially_ordered_set) |
| [Q475023](https://www.wikidata.org/wiki/Q475023) | exact science | sciences that admit of absolute precision in their results | [Exact sciences](https://en.wikipedia.org/wiki/Exact_sciences) |
| [Q483247](https://www.wikidata.org/wiki/Q483247) | phenomenon | any object, fact, or occurrence perceived or observed | [Phenomenon](https://en.wikipedia.org/wiki/Phenomenon) |
| [Q483394](https://www.wikidata.org/wiki/Q483394) | genre | category of creative works based on stylistic, thematic or technical criteria | [Genre](https://en.wikipedia.org/wiki/Genre) |
| [Q483501](https://www.wikidata.org/wiki/Q483501) | artist | person who engages in any form of artistic creation or practice | [Artist](https://en.wikipedia.org/wiki/Artist) |
| [Q484170](https://www.wikidata.org/wiki/Q484170) | commune of France | France territorial subdivision for municipalities | [Communes of France](https://en.wikipedia.org/wiki/Communes_of_France) |
| [Q486902](https://www.wikidata.org/wiki/Q486902) | mathematical model | description of a system using mathematical concepts and language | [Mathematical model](https://en.wikipedia.org/wiki/Mathematical_model) |
| [Q486972](https://www.wikidata.org/wiki/Q486972) | human settlement | place of any size, in which people permanently live | [Human settlement](https://en.wikipedia.org/wiki/Human_settlement) |
| [Q488383](https://www.wikidata.org/wiki/Q488383) | object | anything that may be observed or acted upon by a subject | [Object (philosophy)](https://en.wikipedia.org/wiki/Object_%28philosophy%29) |
| [Q490371](https://www.wikidata.org/wiki/Q490371) | emart | company | [Emart](https://en.wikipedia.org/wiki/Emart) |
| [Q493941](https://www.wikidata.org/wiki/Q493941) | fibration | continuous mapping satisfying the homotopy lifting property with respect to any space | [Fibration](https://en.wikipedia.org/wiki/Fibration) |
| [Q494141](https://www.wikidata.org/wiki/Q494141) | bialgebra | vector space which is both a unital associative algebra and a counital coassociative coalgebra in a compatible way | [Bialgebra](https://en.wikipedia.org/wiki/Bialgebra) |
| [Q494756](https://www.wikidata.org/wiki/Q494756) | data | quantities, characters, or symbols on which operations are performed by a computer | [Data (computer science)](https://en.wikipedia.org/wiki/Data_%28computer_science%29) |
| [Q494823](https://www.wikidata.org/wiki/Q494823) | data format | specification |  |
| [Q500669](https://www.wikidata.org/wiki/Q500669) | technical process | process performed in a technical system | [Process (engineering)](https://en.wikipedia.org/wiki/Process_%28engineering%29) |
| [Q503992](https://www.wikidata.org/wiki/Q503992) | nominal | word class consisting of pronouns, nouns, adjectives and numerals | [Nominal (linguistics)](https://en.wikipedia.org/wiki/Nominal_%28linguistics%29) |
| [Q524778](https://www.wikidata.org/wiki/Q524778) | commissioner | title given to a member of a commission or to an individual who has been given a commission | [Commissioner](https://en.wikipedia.org/wiki/Commissioner) |
| [Q526719](https://www.wikidata.org/wiki/Q526719) | ranking | process of ordering items in a set by criteria | [Ranking](https://en.wikipedia.org/wiki/Ranking) |
| [Q567555](https://www.wikidata.org/wiki/Q567555) | anomaly | deviation beyond what is regarded as normal |  |
| [Q576639](https://www.wikidata.org/wiki/Q576639) | essentially contested concept | concepts having widespread agreement on a concept but not on the best realization thereof | [Essentially contested concept](https://en.wikipedia.org/wiki/Essentially_contested_concept) |
| [Q578779](https://www.wikidata.org/wiki/Q578779) | pure substance | chemical substance composed of atoms or molecules of only one chemical element or chemical compound | [Pure substance](https://en.wikipedia.org/wiki/Pure_substance) |
| [Q582271](https://www.wikidata.org/wiki/Q582271) | noetherian ring | ring whose ideals satisfy the ascending chain condition | [Noetherian ring](https://en.wikipedia.org/wiki/Noetherian_ring) |
| [Q583760](https://www.wikidata.org/wiki/Q583760) | antisymmetric relation | binary relation such that if A is related to B and is different from it then B is not related to A | [Antisymmetric relation](https://en.wikipedia.org/wiki/Antisymmetric_relation) |
| [Q583865](https://www.wikidata.org/wiki/Q583865) | territorial collectivity of France | French public person using its competences autonomously over a particular territory: commune, department, region, overseas collectivity, or territorial collectivity with specific status | [Territorial collectivity](https://en.wikipedia.org/wiki/Territorial_collectivity) |
| [Q591041](https://www.wikidata.org/wiki/Q591041) | scientific publication | publication that reports empirical or theoretical work in the sciences | [Scientific publication](https://en.wikipedia.org/wiki/Scientific_publication) |
| [Q593744](https://www.wikidata.org/wiki/Q593744) | knowledge base | information repository with multiple applications | [Knowledge base](https://en.wikipedia.org/wiki/Knowledge_base) |
| [Q595298](https://www.wikidata.org/wiki/Q595298) | sheaf | collection of objects associated to subsets of a space in a manner admitting gluing and restriction | [Sheaf (mathematics)](https://en.wikipedia.org/wiki/Sheaf_%28mathematics%29) |
| [Q595364](https://www.wikidata.org/wiki/Q595364) | lattice | partially ordered set that admits greatest lower and least upper bounds of any two elements | [Lattice (order)](https://en.wikipedia.org/wiki/Lattice_%28order%29) |
| [Q595523](https://www.wikidata.org/wiki/Q595523) | notion | reflection in the mind of real objects and phenomena in their essential features and relations, distinct from concept | [Notion (philosophy)](https://en.wikipedia.org/wiki/Notion_%28philosophy%29) |
| [Q600590](https://www.wikidata.org/wiki/Q600590) | 𝑛-tuple | finite ordered list of elements | [Tuple](https://en.wikipedia.org/wiki/Tuple) |
| [Q602884](https://www.wikidata.org/wiki/Q602884) | social phenomenon | phenomenon involving multiple organisms reacting to each other | [Social phenomenon](https://en.wikipedia.org/wiki/Social_phenomenon) |
| [Q603880](https://www.wikidata.org/wiki/Q603880) | finite field | field that contains a finite number of elements | [Finite field](https://en.wikipedia.org/wiki/Finite_field) |
| [Q609298](https://www.wikidata.org/wiki/Q609298) | social interaction | interactions between two or more individuals (more narrowly humans) | [Social interaction](https://en.wikipedia.org/wiki/Social_interaction) |
| [Q613930](https://www.wikidata.org/wiki/Q613930) | thematic relation | role that an entity plays with respect to a specific action or state | [Thematic relation](https://en.wikipedia.org/wiki/Thematic_relation) |
| [Q618123](https://www.wikidata.org/wiki/Q618123) | geographical feature | components of planets that can be geographically located | [Geographical feature](https://en.wikipedia.org/wiki/Geographical_feature) |
| [Q619436](https://www.wikidata.org/wiki/Q619436) | quotient ring | construction in abstract algebra | [Quotient ring](https://en.wikipedia.org/wiki/Quotient_ring) |
| [Q621184](https://www.wikidata.org/wiki/Q621184) | problem | situation that invites resolution | [Problem](https://en.wikipedia.org/wiki/Problem) |
| [Q621461](https://www.wikidata.org/wiki/Q621461) | symmetric relation | type of binary relation | [Symmetric relation](https://en.wikipedia.org/wiki/Symmetric_relation) |
| [Q621542](https://www.wikidata.org/wiki/Q621542) | commutative diagram | collection of maps in which all map compositions starting from the same set and ending with the same set give the same result | [Commutative diagram](https://en.wikipedia.org/wiki/Commutative_diagram) |
| [Q621850](https://www.wikidata.org/wiki/Q621850) | reflexive relation | binary relation over a set in which every element is related to itself | [Reflexive relation](https://en.wikipedia.org/wiki/Reflexive_relation) |
| [Q627436](https://www.wikidata.org/wiki/Q627436) | field of work | particular area of activity in industry and science |  |
| [Q628523](https://www.wikidata.org/wiki/Q628523) | message | discrete unit of communication intended by the source for consumption by some recipient or group of recipients | [Message](https://en.wikipedia.org/wiki/Message) |
| [Q629206](https://www.wikidata.org/wiki/Q629206) | computer language | formal language used in communication with a computer | [Computer language](https://en.wikipedia.org/wiki/Computer_language) |
| [Q635162](https://www.wikidata.org/wiki/Q635162) | Hominidae | family of apes | [Hominidae](https://en.wikipedia.org/wiki/Hominidae) |
| [Q638153](https://www.wikidata.org/wiki/Q638153) | semantic wiki | wiki that has an underlying model of the knowledge described in it | [Semantic wiki](https://en.wikipedia.org/wiki/Semantic_wiki) |
| [Q646245](https://www.wikidata.org/wiki/Q646245) | algebraic integer | complex number that solves a monic polynomial with integer coefficients | [Algebraic integer](https://en.wikipedia.org/wiki/Algebraic_integer) |
| [Q646293](https://www.wikidata.org/wiki/Q646293) | informal organization | social structure that governs how people work together | [Informal organization](https://en.wikipedia.org/wiki/Informal_organization) |
| [Q649732](https://www.wikidata.org/wiki/Q649732) | formal system | any well-defined system of abstract thought based on the model of mathematics | [Formal system](https://en.wikipedia.org/wiki/Formal_system) |
| [Q650741](https://www.wikidata.org/wiki/Q650741) | division ring | ring in which division is possible | [Division ring](https://en.wikipedia.org/wiki/Division_ring) |
| [Q651943](https://www.wikidata.org/wiki/Q651943) | signifier | observable aspects of a sign, in semiotics | [Signifiant](https://en.wikipedia.org/wiki/Signifiant) |
| [Q655328](https://www.wikidata.org/wiki/Q655328) | well-formed formula | finite sequence of symbols from a given alphabet that is part of a formal language | [Well-formed formula](https://en.wikipedia.org/wiki/Well-formed_formula) |
| [Q659390](https://www.wikidata.org/wiki/Q659390) | construct | ideal object, whose existence depends upon a subject's mind | [Construct (philosophy)](https://en.wikipedia.org/wiki/Construct_%28philosophy%29) |
| [Q669102](https://www.wikidata.org/wiki/Q669102) | arithmetic calendar | calendar system fixed not from the direct and continuous observation, but by an arithmetic, deterministic and predictive computation, modeling a set of observations with limited precision |  |
| [Q679903](https://www.wikidata.org/wiki/Q679903) | magma | algebraic structure with a binary operation | [Magma (algebra)](https://en.wikipedia.org/wiki/Magma_%28algebra%29) |
| [Q691358](https://www.wikidata.org/wiki/Q691358) | domain-specific language | computer language specialized to a particular application domain | [Domain-specific language](https://en.wikipedia.org/wiki/Domain-specific_language) |
| [Q692689](https://www.wikidata.org/wiki/Q692689) | coproduct | category-theoretic construction which includes as examples the disjoint union of sets and of topological spaces, the free product of groups, and the direct sum of modules and vector spaces | [Coproduct](https://en.wikipedia.org/wiki/Coproduct) |
| [Q693083](https://www.wikidata.org/wiki/Q693083) | soundness | logical term meaning that an argument is valid and its premises are true | [Soundness](https://en.wikipedia.org/wiki/Soundness) |
| [Q694975](https://www.wikidata.org/wiki/Q694975) | electronic document | type of document stored as a computer file | [Electronic document](https://en.wikipedia.org/wiki/Electronic_document) |
| [Q699386](https://www.wikidata.org/wiki/Q699386) | statutory corporation | corporation created by State, varying by jurisdiction in different states | [Statutory corporation](https://en.wikipedia.org/wiki/Statutory_corporation) |
| [Q702492](https://www.wikidata.org/wiki/Q702492) | urban area | large area with high population density and infrastructure of built environment | [Urban area](https://en.wikipedia.org/wiki/Urban_area) |
| [Q707813](https://www.wikidata.org/wiki/Q707813) | Hanseatic city | city in the Hanseatic League | [Lists of former Hansa cities](https://en.wikipedia.org/wiki/Lists_of_former_Hansa_cities) |
| [Q713084](https://www.wikidata.org/wiki/Q713084) | artinian ring | ring that satisfies the descending chain condition on ideals | [Artinian ring](https://en.wikipedia.org/wiki/Artinian_ring) |
| [Q714737](https://www.wikidata.org/wiki/Q714737) | category of being | philosophical concept | [Theory of categories](https://en.wikipedia.org/wiki/Theory_of_categories) |
| [Q719395](https://www.wikidata.org/wiki/Q719395) | category | algebraic structure of objects and morphisms between objects, which can be associatively composed if the (co)domains agree | [Category (mathematics)](https://en.wikipedia.org/wiki/Category_%28mathematics%29) |
| [Q720069](https://www.wikidata.org/wiki/Q720069) | nuclear family | family group consisting of parents and their children (one or more) | [Nuclear family](https://en.wikipedia.org/wiki/Nuclear_family) |
| [Q724975](https://www.wikidata.org/wiki/Q724975) | Gaussian integer | complex number whose real and imaginary parts are both integers | [Gaussian integer](https://en.wikipedia.org/wiki/Gaussian_integer) |
| [Q726212](https://www.wikidata.org/wiki/Q726212) | bounded set | set is called bounded, if it is, in a certain sense, of finite size | [Bounded set](https://en.wikipedia.org/wiki/Bounded_set) |
| [Q732577](https://www.wikidata.org/wiki/Q732577) | publication | content made available to the general public | [Publication](https://en.wikipedia.org/wiki/Publication) |
| [Q733541](https://www.wikidata.org/wiki/Q733541) | consequence | imperative or possible inference |  |
| [Q739925](https://www.wikidata.org/wiki/Q739925) | family of sets | collection of some of the subsets of a set; collection of any sets whatsoever | [Family of sets](https://en.wikipedia.org/wiki/Family_of_sets) |
| [Q743418](https://www.wikidata.org/wiki/Q743418) | octonion | non-commutative, non-associative algebra of numbers with eight real components | [Octonion](https://en.wikipedia.org/wiki/Octonion) |
| [Q748349](https://www.wikidata.org/wiki/Q748349) | mathematical structure | combination of a set and an extra structure on it; more precisely, an object of a concrete category | [Mathematical structure](https://en.wikipedia.org/wiki/Mathematical_structure) |
| [Q750843](https://www.wikidata.org/wiki/Q750843) | information processing | process in which input information is analysed or transformed in order to produce information as output | [Information processing (psychology)](https://en.wikipedia.org/wiki/Information_processing_%28psychology%29) |
| [Q751969](https://www.wikidata.org/wiki/Q751969) | coset | the set arising from multiplying every element in a subgroup by an element in the ambient group | [Coset](https://en.wikipedia.org/wiki/Coset) |
| [Q753127](https://www.wikidata.org/wiki/Q753127) | topological sorting | an ordering of the vertices of the directed graph for which each edge is directed from earlier to later in the ordering | [Topological sorting](https://en.wikipedia.org/wiki/Topological_sorting) |
| [Q765994](https://www.wikidata.org/wiki/Q765994) | group object | analogue of the definition of a group inside an arbitrary category | [Group object](https://en.wikipedia.org/wiki/Group_object) |
| [Q769620](https://www.wikidata.org/wiki/Q769620) | social action | act which takes into account the actions and reactions of (other) individuals or agents | [Social action](https://en.wikipedia.org/wiki/Social_action) |
| [Q774347](https://www.wikidata.org/wiki/Q774347) | consanguinity | property of being from the same kinship as another person; quality of being descended from the same ancestor as another person | [Consanguinity](https://en.wikipedia.org/wiki/Consanguinity) |
| [Q781413](https://www.wikidata.org/wiki/Q781413) | cognitive process |  | [Cognitive process](https://en.wikipedia.org/wiki/Cognitive_process) |
| [Q783794](https://www.wikidata.org/wiki/Q783794) | company | legal entity representing an association of people, whether natural, legal or a mixture of both, with a specific objective | [Company](https://en.wikipedia.org/wiki/Company) |
| [Q785260](https://www.wikidata.org/wiki/Q785260) | phase of human life | stage in the development of a human being |  |
| [Q788790](https://www.wikidata.org/wiki/Q788790) | documentation | any communicable material that is used to describe, explain or instruct regarding some attributes of an object, system or procedure | [Documentation](https://en.wikipedia.org/wiki/Documentation) |
| [Q789016](https://www.wikidata.org/wiki/Q789016) | content word | word that name objects of reality and their qualities, e.g. living things, family members, natural phenomena, common actions, characteristics; mostly nouns (“dog”), lexical verbs (“eat”), adjectives (“happy”), and adverbs (“happily“) | [Content word](https://en.wikipedia.org/wiki/Content_word) |
| [Q795052](https://www.wikidata.org/wiki/Q795052) | individual | individual person or organism | [Individual](https://en.wikipedia.org/wiki/Individual) |
| [Q797769](https://www.wikidata.org/wiki/Q797769) | peer production system | production of goods and services that relies on self-organizing communities of individuals | [Peer production](https://en.wikipedia.org/wiki/Peer_production) |
| [Q803531](https://www.wikidata.org/wiki/Q803531) | quadratic integer | algebraic integer of a given quadratic field | [Quadratic integer](https://en.wikipedia.org/wiki/Quadratic_integer) |
| [Q803935](https://www.wikidata.org/wiki/Q803935) | Baire function | functions obtained from continuous functions by transfinite iteration of the operation of forming pointwise limits of sequences of functions | [Baire function](https://en.wikipedia.org/wiki/Baire_function) |
| [Q813912](https://www.wikidata.org/wiki/Q813912) | condition | relative state or circumstances of some object or event |  |
| [Q816264](https://www.wikidata.org/wiki/Q816264) | formal science | set of disciplines concerned with formal systems, such as logic, mathematics, and game theory | [Formal science](https://en.wikipedia.org/wiki/Formal_science) |
| [Q818895](https://www.wikidata.org/wiki/Q818895) | computable number | real number that can be computed to within any desired precision by a finite, terminating algorithm | [Computable number](https://en.wikipedia.org/wiki/Computable_number) |
| [Q826165](https://www.wikidata.org/wiki/Q826165) | Web Ontology Language | family of knowledge representation languages | [Web Ontology Language](https://en.wikipedia.org/wiki/Web_Ontology_Language) |
| [Q827335](https://www.wikidata.org/wiki/Q827335) | abstract data type | mathematical model for data types | [Abstract data type](https://en.wikipedia.org/wiki/Abstract_data_type) |
| [Q828224](https://www.wikidata.org/wiki/Q828224) | kilometre | SI unit of length equal to one thousand metres | [Kilometre](https://en.wikipedia.org/wiki/Kilometre) |
| [Q836915](https://www.wikidata.org/wiki/Q836915) | free state | form of government | [Free state (polity)](https://en.wikipedia.org/wiki/Free_state_%28polity%29) |
| [Q837414](https://www.wikidata.org/wiki/Q837414) | hypercomplex number | element of a unital algebra over the field of real numbers | [Hypercomplex number](https://en.wikipedia.org/wiki/Hypercomplex_number) |
| [Q837495](https://www.wikidata.org/wiki/Q837495) | meronymy | semantic relation specific to linguistics | [Meronymy](https://en.wikipedia.org/wiki/Meronymy) |
| [Q837766](https://www.wikidata.org/wiki/Q837766) | local authority | corporation below the sovereign state level that has its own deliberative assembly |  |
| [Q838948](https://www.wikidata.org/wiki/Q838948) | work of art | aesthetic item or artistic creation of aesthetic value | [Work of art](https://en.wikipedia.org/wiki/Work_of_art) |
| [Q839578](https://www.wikidata.org/wiki/Q839578) | group dynamics | system of behaviors and psychological processes occurring within a social group or between social groups | [Group dynamics](https://en.wikipedia.org/wiki/Group_dynamics) |
| [Q840247](https://www.wikidata.org/wiki/Q840247) | hypergraph | generalized undirected graph in which generalized edges connect one, two, or more nodes | [Hypergraph](https://en.wikipedia.org/wiki/Hypergraph) |
| [Q843237](https://www.wikidata.org/wiki/Q843237) | diagram | collection of objects and morphisms in a category | [Diagram (category theory)](https://en.wikipedia.org/wiki/Diagram_%28category_theory%29) |
| [Q845739](https://www.wikidata.org/wiki/Q845739) | query language | computer language used to make queries into databases and information systems such as SQL or XQuery | [Query language](https://en.wikipedia.org/wiki/Query_language) |
| [Q853614](https://www.wikidata.org/wiki/Q853614) | identifier | name that identifies either a unique object or a unique class of objects | [Identifier](https://en.wikipedia.org/wiki/Identifier) |
| [Q853725](https://www.wikidata.org/wiki/Q853725) | social relation | voluntary or involuntary interpersonal relationship between individuals within or between groups; fundamental unit of social science analysis that aggregates into social structures reflecting kinship, class, institution, or gender | [Social relation](https://en.wikipedia.org/wiki/Social_relation) |
| [Q854457](https://www.wikidata.org/wiki/Q854457) | complex system | system composed of many interacting components | [Complex system](https://en.wikipedia.org/wiki/Complex_system) |
| [Q856215](https://www.wikidata.org/wiki/Q856215) | indexed family | collection of objects, each associated with an index from some index set | [Indexed family](https://en.wikipedia.org/wiki/Indexed_family) |
| [Q858656](https://www.wikidata.org/wiki/Q858656) | commutative ring | algebraic structure | [Commutative ring](https://en.wikipedia.org/wiki/Commutative_ring) |
| [Q864213](https://www.wikidata.org/wiki/Q864213) | Conservative extension | area of research | [Conservative extension](https://en.wikipedia.org/wiki/Conservative_extension) |
| [Q864377](https://www.wikidata.org/wiki/Q864377) | multiset | set (in mathematics) with repetitions allowed | [Multiset](https://en.wikipedia.org/wiki/Multiset) |
| [Q864475](https://www.wikidata.org/wiki/Q864475) | functor | in category theory, a mapping between categories that preserves their structure (identity morphisms, composition of morphisms) | [Functor](https://en.wikipedia.org/wiki/Functor) |
| [Q867345](https://www.wikidata.org/wiki/Q867345) | Euclidean domain | Commutative ring with an Euclidean division | [Euclidean domain](https://en.wikipedia.org/wiki/Euclidean_domain) |
| [Q868169](https://www.wikidata.org/wiki/Q868169) | group homomorphism | function between groups that preserves multiplication structure | [Group homomorphism](https://en.wikipedia.org/wiki/Group_homomorphism) |
| [Q874405](https://www.wikidata.org/wiki/Q874405) | social group | two or more humans who interact with one another | [Social group](https://en.wikipedia.org/wiki/Social_group) |
| [Q874429](https://www.wikidata.org/wiki/Q874429) | group theory | branch of mathematics that studies the algebraic properties of groups | [Group theory](https://en.wikipedia.org/wiki/Group_theory) |
| [Q895526](https://www.wikidata.org/wiki/Q895526) | governing body | a designated body with authority | [Governing body](https://en.wikipedia.org/wiki/Governing_body) |
| [Q897395](https://www.wikidata.org/wiki/Q897395) | executive board | executive board of a corporation (public limited company) | [Vorstand](https://en.wikipedia.org/wiki/Vorstand) |
| [Q899523](https://www.wikidata.org/wiki/Q899523) | object-based language | programming language | [Object-based language](https://en.wikipedia.org/wiki/Object-based_language) |
| [Q902805](https://www.wikidata.org/wiki/Q902805) | primary nutritional group | group of organisms, divided in relation to the nutrition mode according to the sources of energy and carbon, needed for living, growth and reproduction | [Primary nutritional groups](https://en.wikipedia.org/wiki/Primary_nutritional_groups) |
| [Q902814](https://www.wikidata.org/wiki/Q902814) | border city | town or city on a border between larger political areas | [Border town](https://en.wikipedia.org/wiki/Border_town) |
| [Q903820](https://www.wikidata.org/wiki/Q903820) | field theory | theory in mathematics | [Field theory (mathematics)](https://en.wikipedia.org/wiki/Field_theory_%28mathematics%29) |
| [Q908049](https://www.wikidata.org/wiki/Q908049) | bound state | system where a particle is subject to a potential such that the particle has a tendency to remain localised in one or more regions of space | [Bound state](https://en.wikipedia.org/wiki/Bound_state) |
| [Q921513](https://www.wikidata.org/wiki/Q921513) | social behavior | behavior among two or more organisms, typically from the same species | [Social behavior](https://en.wikipedia.org/wiki/Social_behavior) |
| [Q930933](https://www.wikidata.org/wiki/Q930933) | relation | general relation between different objects or individuals | [Relation (philosophy)](https://en.wikipedia.org/wiki/Relation_%28philosophy%29) |
| [Q931483](https://www.wikidata.org/wiki/Q931483) | legal fiction | fact assumed or created by courts which is then used in order to apply a legal rule | [Legal fiction](https://en.wikipedia.org/wiki/Legal_fiction) |
| [Q937228](https://www.wikidata.org/wiki/Q937228) | property | predominant feature that characterizes a being, a thing, a phenomenon, etc. and which differentiates one being from another, one thing from another | [Property (philosophy)](https://en.wikipedia.org/wiki/Property_%28philosophy%29) |
| [Q942423](https://www.wikidata.org/wiki/Q942423) | projective module | in algebra, a module that is the direct summand of a free module | [Projective module](https://en.wikipedia.org/wiki/Projective_module) |
| [Q948571](https://www.wikidata.org/wiki/Q948571) | organ of state | body with power given by the state |  |
| [Q951437](https://www.wikidata.org/wiki/Q951437) | level of measurement | classification that describes the nature of information within the numbers assigned to variables | [Level of measurement](https://en.wikipedia.org/wiki/Level_of_measurement) |
| [Q960648](https://www.wikidata.org/wiki/Q960648) | point of interest | specific location that someone may find useful or interesting | [Point of interest](https://en.wikipedia.org/wiki/Point_of_interest) |
| [Q980357](https://www.wikidata.org/wiki/Q980357) | grammatical category | analytical class within the grammar of a language | [Grammatical category](https://en.wikipedia.org/wiki/Grammatical_category) |
| [Q994895](https://www.wikidata.org/wiki/Q994895) | technical system | system created through engineering |  |
| [Q999234](https://www.wikidata.org/wiki/Q999234) | scientific term | technical term: word or expression that is part of scientific terminology |  |
| [Q1000660](https://www.wikidata.org/wiki/Q1000660) | algebra over a field | vector space equipped with a bilinear product | [Algebra over a field](https://en.wikipedia.org/wiki/Algebra_over_a_field) |
| [Q1004415](https://www.wikidata.org/wiki/Q1004415) | run-time system | system that provides behavior needed by running code; primarily implements portions of an execution model | [Runtime system](https://en.wikipedia.org/wiki/Runtime_system) |
| [Q1028181](https://www.wikidata.org/wiki/Q1028181) | painter | artist who practices painting | [Painter](https://en.wikipedia.org/wiki/Painter) |
| [Q1045785](https://www.wikidata.org/wiki/Q1045785) | semantic network | directed graph structure with labeled edges serving to encode and represent knowledge, whether knowledge of definitions or assertions | [Semantic network](https://en.wikipedia.org/wiki/Semantic_network) |
| [Q1047113](https://www.wikidata.org/wiki/Q1047113) | field of study | field limited to a specific area of ​​knowledge; specialization in an occupation or branch of learning; a specific use |  |
| [Q1047307](https://www.wikidata.org/wiki/Q1047307) | bundle | generalization of a fiber bundle dropping the condition of a local product structure | [Bundle (mathematics)](https://en.wikipedia.org/wiki/Bundle_%28mathematics%29) |
| [Q1048835](https://www.wikidata.org/wiki/Q1048835) | political territorial entity | region accepted to be in the jurisdiction of a particular government entity |  |
| [Q1052579](https://www.wikidata.org/wiki/Q1052579) | unique factorization domain | integral domain where every nonzero element is uniquely expressible as a product of prime elements | [Unique factorization domain](https://en.wikipedia.org/wiki/Unique_factorization_domain) |
| [Q1056428](https://www.wikidata.org/wiki/Q1056428) | type theory | study of type systems in mathematical logic and computer science | [Type theory](https://en.wikipedia.org/wiki/Type_theory) |
| [Q1062242](https://www.wikidata.org/wiki/Q1062242) | Grothendieck topology | structure on a category C which makes the objects of C act like the open sets of a topological space | [Grothendieck topology](https://en.wikipedia.org/wiki/Grothendieck_topology) |
| [Q1063239](https://www.wikidata.org/wiki/Q1063239) | polity | group of people with a collective identity | [Polity](https://en.wikipedia.org/wiki/Polity) |
| [Q1063801](https://www.wikidata.org/wiki/Q1063801) | tertiary source | index or textual consolidation of primary and secondary sources | [Tertiary source](https://en.wikipedia.org/wiki/Tertiary_source) |
| [Q1066984](https://www.wikidata.org/wiki/Q1066984) | financial center | city that is home to a large number of internationally significant banks, businesses, and stock exchanges | [Financial centre](https://en.wikipedia.org/wiki/Financial_centre) |
| [Q1068473](https://www.wikidata.org/wiki/Q1068473) | educational technology | use of technology in education to improve learning and teaching; not restricted to high technology | [Educational technology](https://en.wikipedia.org/wiki/Educational_technology) |
| [Q1069998](https://www.wikidata.org/wiki/Q1069998) | partial order | reflexive antisymmetric transitive binary relation | [Partial order](https://en.wikipedia.org/wiki/Partial_order) |
| [Q1076486](https://www.wikidata.org/wiki/Q1076486) | sports venue | facility (building, structure, or place) dedicated to sports | [Sports venue](https://en.wikipedia.org/wiki/Sports_venue) |
| [Q1076968](https://www.wikidata.org/wiki/Q1076968) | digital media | any media encoded in machine-readable formats | [Digital media](https://en.wikipedia.org/wiki/Digital_media) |
| [Q1082709](https://www.wikidata.org/wiki/Q1082709) | Hukawng Valley | valley | [Hukawng Valley](https://en.wikipedia.org/wiki/Hukawng_Valley) |
| [Q1082992](https://www.wikidata.org/wiki/Q1082992) | equivalence of categories | abstract mathematics relationship | [Equivalence of categories](https://en.wikipedia.org/wiki/Equivalence_of_categories) |
| [Q1097991](https://www.wikidata.org/wiki/Q1097991) | irreflexive relation | type of binary relation | [Irreflexive relation](https://en.wikipedia.org/wiki/Irreflexive_relation) |
| [Q1115376](https://www.wikidata.org/wiki/Q1115376) | egg donation | method of assisted reproduction | [Egg donation](https://en.wikipedia.org/wiki/Egg_donation) |
| [Q1128340](https://www.wikidata.org/wiki/Q1128340) | subject heading | lexical unit of a thesaurus (word or phrase) used for indexing and that captures the essence of the topic of a document | [Index term](https://en.wikipedia.org/wiki/Index_term) |
| [Q1129622](https://www.wikidata.org/wiki/Q1129622) | self-reference | sentence, idea or formula that refers to itself | [Self-reference](https://en.wikipedia.org/wiki/Self-reference) |
| [Q1130645](https://www.wikidata.org/wiki/Q1130645) | open-source software | software that anyone is free to use and redistribute in its current state with a permissive licence giving a libre access to its original source code (but not necessarily to modify it) | [Open-source software](https://en.wikipedia.org/wiki/Open-source_software) |
| [Q1132455](https://www.wikidata.org/wiki/Q1132455) | hazard | source of a potential threat | [Hazard](https://en.wikipedia.org/wiki/Hazard) |
| [Q1132952](https://www.wikidata.org/wiki/Q1132952) | homogeneous function | function with multiplicative scaling behaviour | [Homogeneous function](https://en.wikipedia.org/wiki/Homogeneous_function) |
| [Q1137726](https://www.wikidata.org/wiki/Q1137726) | directed graph | graph with oriented edges | [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) |
| [Q1143969](https://www.wikidata.org/wiki/Q1143969) | principal ideal domain | Algebraic structure | [Principal ideal domain](https://en.wikipedia.org/wiki/Principal_ideal_domain) |
| [Q1144694](https://www.wikidata.org/wiki/Q1144694) | duty of care | legal obligation to provide reasonable care when performing an activity that could harm others | [Duty of care](https://en.wikipedia.org/wiki/Duty_of_care) |
| [Q1144882](https://www.wikidata.org/wiki/Q1144882) | declarative programming language | type of programming language |  |
| [Q1147242](https://www.wikidata.org/wiki/Q1147242) | symmetric difference | mathematical definition in set theory | [Symmetric difference](https://en.wikipedia.org/wiki/Symmetric_difference) |
| [Q1148924](https://www.wikidata.org/wiki/Q1148924) | Kolmogorov space | concept in topology | [Kolmogorov space](https://en.wikipedia.org/wiki/Kolmogorov_space) |
| [Q1150070](https://www.wikidata.org/wiki/Q1150070) | change | process, event or action that deviates from the present state | [Change (philosophy)](https://en.wikipedia.org/wiki/Change_%28philosophy%29) |
| [Q1151067](https://www.wikidata.org/wiki/Q1151067) | rule | prescription, including laws, regulations, instructions, guidelines, and social conventions; determinate method for performing any operation |  |
| [Q1154996](https://www.wikidata.org/wiki/Q1154996) | fiber bundle | continuous surjection satisfying a local triviality condition | [Fiber bundle](https://en.wikipedia.org/wiki/Fiber_bundle) |
| [Q1156402](https://www.wikidata.org/wiki/Q1156402) | reasoning | type of thought and capacity of consciously making sense of things, applying logic, and adapting or justifying practices, institutions, and beliefs based on new or existing information | [Reasoning](https://en.wikipedia.org/wiki/Reasoning) |
| [Q1166618](https://www.wikidata.org/wiki/Q1166618) | mathematical logic | subfield of mathematics | [Mathematical logic](https://en.wikipedia.org/wiki/Mathematical_logic) |
| [Q1166625](https://www.wikidata.org/wiki/Q1166625) | mathematical problem | problem that can be possibly solved via mathematics | [Mathematical problem](https://en.wikipedia.org/wiki/Mathematical_problem) |
| [Q1172284](https://www.wikidata.org/wiki/Q1172284) | data set | collection of data, publication type | [Data set](https://en.wikipedia.org/wiki/Data_set) |
| [Q1172400](https://www.wikidata.org/wiki/Q1172400) | data terminal equipment | communications system equipment | [Data terminal equipment](https://en.wikipedia.org/wiki/Data_terminal_equipment) |
| [Q1172480](https://www.wikidata.org/wiki/Q1172480) | data model | an abstract model that organizes elements of data and standardizes how they relate to one another and to real world entities. | [Data model](https://en.wikipedia.org/wiki/Data_model) |
| [Q1182260](https://www.wikidata.org/wiki/Q1182260) | data deduplication | data processing technique to eliminate duplicate copies of repeating data | [Data deduplication](https://en.wikipedia.org/wiki/Data_deduplication) |
| [Q1183543](https://www.wikidata.org/wiki/Q1183543) | device | artificial object with which something can be worked on, manufactured or effected |  |
| [Q1184244](https://www.wikidata.org/wiki/Q1184244) | delict | civil wrong | [Delict](https://en.wikipedia.org/wiki/Delict) |
| [Q1187811](https://www.wikidata.org/wiki/Q1187811) | college town | community dominated by its university population | [College town](https://en.wikipedia.org/wiki/College_town) |
| [Q1189753](https://www.wikidata.org/wiki/Q1189753) | denotation | literal meaning of a sign, more or less like dictionaries try to define it | [Denotation](https://en.wikipedia.org/wiki/Denotation) |
| [Q1190554](https://www.wikidata.org/wiki/Q1190554) | occurrence | expression and recorded history of an event or events including participating agents and transpired activities |  |
| [Q1191433](https://www.wikidata.org/wiki/Q1191433) | completely regular space | topological space in which a point and a closed set are separable by a real-valued continuous function | [Tychonoff space](https://en.wikipedia.org/wiki/Tychonoff_space) |
| [Q1193907](https://www.wikidata.org/wiki/Q1193907) | link rot | phenomenon in which URLs gradually tend to cease functioning | [Link rot](https://en.wikipedia.org/wiki/Link_rot) |
| [Q1194916](https://www.wikidata.org/wiki/Q1194916) | mereology | study of parts and the wholes they form | [Mereology](https://en.wikipedia.org/wiki/Mereology) |
| [Q1195339](https://www.wikidata.org/wiki/Q1195339) | directed acyclic graph | directed graph with no directed cycles | [Directed acyclic graph](https://en.wikipedia.org/wiki/Directed_acyclic_graph) |
| [Q1196038](https://www.wikidata.org/wiki/Q1196038) | groupoid | category where every morphism is invertible; generalization of a group | [Groupoid](https://en.wikipedia.org/wiki/Groupoid) |
| [Q1200957](https://www.wikidata.org/wiki/Q1200957) | tourist destination | place attracting many tourists | [Tourist destination](https://en.wikipedia.org/wiki/Tourist_destination) |
| [Q1200992](https://www.wikidata.org/wiki/Q1200992) | abstraction layer | way of hiding details of a computing subsystem, allowing separation of concerns and interoperability | [Abstraction layer](https://en.wikipedia.org/wiki/Abstraction_layer) |
| [Q1207505](https://www.wikidata.org/wiki/Q1207505) | quality | distinguishing feature | [Quality (philosophy)](https://en.wikipedia.org/wiki/Quality_%28philosophy%29) |
| [Q1209283](https://www.wikidata.org/wiki/Q1209283) | electronic media | media that use electronics or electromechanical energy for the audience to access the content | [Electronic media](https://en.wikipedia.org/wiki/Electronic_media) |
| [Q1211071](https://www.wikidata.org/wiki/Q1211071) | equivalence class | mathematical concept | [Equivalence class](https://en.wikipedia.org/wiki/Equivalence_class) |
| [Q1217379](https://www.wikidata.org/wiki/Q1217379) | parenting | process of raising a child | [Parenting](https://en.wikipedia.org/wiki/Parenting) |
| [Q1221156](https://www.wikidata.org/wiki/Q1221156) | federated state of Germany | administrative division of the Federal Republic of Germany | [States of Germany](https://en.wikipedia.org/wiki/States_of_Germany) |
| [Q1224487](https://www.wikidata.org/wiki/Q1224487) | equaliser | type of limit in category theory | [Equaliser (mathematics)](https://en.wikipedia.org/wiki/Equaliser_%28mathematics%29) |
| [Q1224764](https://www.wikidata.org/wiki/Q1224764) | ontology alignment | process of determining correspondences between concepts | [Ontology alignment](https://en.wikipedia.org/wiki/Ontology_alignment) |
| [Q1244890](https://www.wikidata.org/wiki/Q1244890) | rational number | quotient of two integers | [Rational number](https://en.wikipedia.org/wiki/Rational_number) |
| [Q1260632](https://www.wikidata.org/wiki/Q1260632) | content | information and experiences that are directed toward an end-user or audience | [Content (media)](https://en.wikipedia.org/wiki/Content_%28media%29) |
| [Q1263068](https://www.wikidata.org/wiki/Q1263068) | duplicate entry | duplicate database entry (see Q17362920 Wikimedia duplicated page); reason for deprecation |  |
| [Q1266546](https://www.wikidata.org/wiki/Q1266546) | record linkage | joining records or entities from different data sets that may or may not share a common identifier and matching the entities based on their properties | [Record linkage](https://en.wikipedia.org/wiki/Record_linkage) |
| [Q1268980](https://www.wikidata.org/wiki/Q1268980) | dynamic programming language | programming language that supports manipulating program constructs at runtime | [Dynamic programming language](https://en.wikipedia.org/wiki/Dynamic_programming_language) |
| [Q1269299](https://www.wikidata.org/wiki/Q1269299) | type of business entity | legal form of business entity | [Type of business entity](https://en.wikipedia.org/wiki/Type_of_business_entity) |
| [Q1272626](https://www.wikidata.org/wiki/Q1272626) | representation | entity or process that portrays something else, usually in a simplified or approximated manner |  |
| [Q1281618](https://www.wikidata.org/wiki/Q1281618) | sculptor | artist specializing in sculpture | [Sculptor](https://en.wikipedia.org/wiki/Sculptor) |
| [Q1292119](https://www.wikidata.org/wiki/Q1292119) | style | manner of expression particular to a specific period, group, or person |  |
| [Q1292333](https://www.wikidata.org/wiki/Q1292333) | free module | in algebra, a module that has a basis | [Free module](https://en.wikipedia.org/wiki/Free_module) |
| [Q1293220](https://www.wikidata.org/wiki/Q1293220) | physical phenomenon | phenomenon of the material world | [Physical phemomenon](https://en.wikipedia.org/wiki/Physical_phemomenon) |
| [Q1293664](https://www.wikidata.org/wiki/Q1293664) | open content | content that is openly accessible and modifiable to others | [Open content](https://en.wikipedia.org/wiki/Open_content) |
| [Q1304193](https://www.wikidata.org/wiki/Q1304193) | node | unit connected by edges with other units in a graph, in graph theory | [Vertex (graph theory)](https://en.wikipedia.org/wiki/Vertex_%28graph_theory%29) |
| [Q1306755](https://www.wikidata.org/wiki/Q1306755) | administrative centre | seat of regional administration or local government, or a county town, or the place where the central administration of a commune is located | [Administrative centre](https://en.wikipedia.org/wiki/Administrative_centre) |
| [Q1307214](https://www.wikidata.org/wiki/Q1307214) | form of government | Wikidata metaclass for government in terms of organisational model or type | [Form of government](https://en.wikipedia.org/wiki/Form_of_government) |
| [Q1307779](https://www.wikidata.org/wiki/Q1307779) | integrated municipality | type of municipality in Germany, Austria and Switzerland |  |
| [Q1308999](https://www.wikidata.org/wiki/Q1308999) | restriction | mathematical function | [Restriction (mathematics)](https://en.wikipedia.org/wiki/Restriction_%28mathematics%29) |
| [Q1313923](https://www.wikidata.org/wiki/Q1313923) | kindred | group of related persons |  |
| [Q1321926](https://www.wikidata.org/wiki/Q1321926) | constructible number | real number that can be geometrically constructed with compass and straightedge from a unit segment in a finite number of steps | [Constructible number](https://en.wikipedia.org/wiki/Constructible_number) |
| [Q1322005](https://www.wikidata.org/wiki/Q1322005) | natural phenomenon | observable phenomenon which is not human-made |  |
| [Q1322494](https://www.wikidata.org/wiki/Q1322494) | sociotope | defined space that is uniform in its use values and social meanings | [Sociotope](https://en.wikipedia.org/wiki/Sociotope) |
| [Q1322614](https://www.wikidata.org/wiki/Q1322614) | limit | category theory term | [Limit (category theory)](https://en.wikipedia.org/wiki/Limit_%28category_theory%29) |
| [Q1328323](https://www.wikidata.org/wiki/Q1328323) | functionary | person with leadership position within an organization | [Functionary](https://en.wikipedia.org/wiki/Functionary) |
| [Q1333055](https://www.wikidata.org/wiki/Q1333055) | semiring | algebraic structure similar to a ring, but not necessarily with additive inverses | [Semiring](https://en.wikipedia.org/wiki/Semiring) |
| [Q1335186](https://www.wikidata.org/wiki/Q1335186) | extensive function |  |  |
| [Q1341685](https://www.wikidata.org/wiki/Q1341685) | inference engine | component of the system that applies logical rules to the knowledge base to deduce new information | [Inference engine](https://en.wikipedia.org/wiki/Inference_engine) |
| [Q1347208](https://www.wikidata.org/wiki/Q1347208) | epimorphism | right-cancellative morphism | [Epimorphism](https://en.wikipedia.org/wiki/Epimorphism) |
| [Q1347367](https://www.wikidata.org/wiki/Q1347367) | aptitude | ability to perform an action or fulfill a role | [Aptitude](https://en.wikipedia.org/wiki/Aptitude) |
| [Q1348645](https://www.wikidata.org/wiki/Q1348645) | instructional materials | print or other media used to impart knowledge or teach skills | [Instructional materials](https://en.wikipedia.org/wiki/Instructional_materials) |
| [Q1361526](https://www.wikidata.org/wiki/Q1361526) | reachability | whether one vertex can be reached from another in a graph | [Reachability](https://en.wikipedia.org/wiki/Reachability) |
| [Q1367590](https://www.wikidata.org/wiki/Q1367590) | legal relationship | relationship between subjects of law | [Legal relationship](https://en.wikipedia.org/wiki/Legal_relationship) |
| [Q1370617](https://www.wikidata.org/wiki/Q1370617) | measurement scale | graduated measurement scheme developed for a phenomenon |  |
| [Q1379672](https://www.wikidata.org/wiki/Q1379672) | evaluation | determination of a subject's merit, worth, scope or significance | [Evaluation](https://en.wikipedia.org/wiki/Evaluation) |
| [Q1391420](https://www.wikidata.org/wiki/Q1391420) | specialized literature | branch of non-fiction literature |  |
| [Q1397073](https://www.wikidata.org/wiki/Q1397073) | data schema | type of information model |  |
| [Q1397439](https://www.wikidata.org/wiki/Q1397439) | pullback | category-theoretic limit of a diagram of the form 𝑋→𝑍←𝑌 | [Pullback (category theory)](https://en.wikipedia.org/wiki/Pullback_%28category_theory%29) |
| [Q1413406](https://www.wikidata.org/wiki/Q1413406) | technical documentation | description of a technical product and its handling, functionality and architecture | [Technical documentation](https://en.wikipedia.org/wiki/Technical_documentation) |
| [Q1413749](https://www.wikidata.org/wiki/Q1413749) | scale | system of reference values for a characteristic |  |
| [Q1415187](https://www.wikidata.org/wiki/Q1415187) | economic agent | actor and decision maker in an economic model | [Agent (economics)](https://en.wikipedia.org/wiki/Agent_%28economics%29) |
| [Q1417809](https://www.wikidata.org/wiki/Q1417809) | universal property | central object of study in category theory | [Universal property](https://en.wikipedia.org/wiki/Universal_property) |
| [Q1418640](https://www.wikidata.org/wiki/Q1418640) | local government in Germany | type of governmental entity in Germany |  |
| [Q1422929](https://www.wikidata.org/wiki/Q1422929) | primate city | disproportionately large city in its country or region | [Primate city](https://en.wikipedia.org/wiki/Primate_city) |
| [Q1425985](https://www.wikidata.org/wiki/Q1425985) | preorder | reflexive and transitive binary relation | [Preorder](https://en.wikipedia.org/wiki/Preorder) |
| [Q1426191](https://www.wikidata.org/wiki/Q1426191) | flat module | module such that taking the tensor product with it induces an exact functor | [Flat module](https://en.wikipedia.org/wiki/Flat_module) |
| [Q1437361](https://www.wikidata.org/wiki/Q1437361) | form of art | way in which the elements of an art work are organised in contrast to its content |  |
| [Q1437394](https://www.wikidata.org/wiki/Q1437394) | formal concept analysis | a rigorous method of deriving an ontology from a collection of objects and their properties | [Formal concept analysis](https://en.wikipedia.org/wiki/Formal_concept_analysis) |
| [Q1442189](https://www.wikidata.org/wiki/Q1442189) | natural transformation | transformation between two functors studied in category theory | [Natural transformation](https://en.wikipedia.org/wiki/Natural_transformation) |
| [Q1454986](https://www.wikidata.org/wiki/Q1454986) | physical system | portion of the physical universe chosen for analysis; everything outside the system is known as the environment | [Physical system](https://en.wikipedia.org/wiki/Physical_system) |
| [Q1456832](https://www.wikidata.org/wiki/Q1456832) | violation of law | action against the law, subject to punishment | [Violation of law](https://en.wikipedia.org/wiki/Violation_of_law) |
| [Q1467124](https://www.wikidata.org/wiki/Q1467124) | simplicial set | construction in categorical homotopy theory; contravariant functor from the simplex category to the category of sets | [Simplicial set](https://en.wikipedia.org/wiki/Simplicial_set) |
| [Q1469824](https://www.wikidata.org/wiki/Q1469824) | controlled vocabulary | standardized and organized sets of words and phrases for retrieval and disambiguation of information, distinguishing preferred terms from non-preferred terms | [Controlled vocabulary](https://en.wikipedia.org/wiki/Controlled_vocabulary) |
| [Q1485500](https://www.wikidata.org/wiki/Q1485500) | tangible good | physical asset which is the subject of trade or could come as an object of trade turnover into consideration | [Economic good](https://en.wikipedia.org/wiki/Economic_good) |
| [Q1489259](https://www.wikidata.org/wiki/Q1489259) | superpower | state with a leading position in the international system and the ability to influence events in its own interest by global projection of power | [Superpower](https://en.wikipedia.org/wiki/Superpower) |
| [Q1491747](https://www.wikidata.org/wiki/Q1491747) | Galois connection | pair of adjoint functors between two preordered sets seen as categories | [Galois connection](https://en.wikipedia.org/wiki/Galois_connection) |
| [Q1491995](https://www.wikidata.org/wiki/Q1491995) | connected space | topological space that cannot be written as the disjoint union of two nonempty open subsets | [Connected space](https://en.wikipedia.org/wiki/Connected_space) |
| [Q1501387](https://www.wikidata.org/wiki/Q1501387) | transitive closure | operation on binary relations | [Transitive closure](https://en.wikipedia.org/wiki/Transitive_closure) |
| [Q1502246](https://www.wikidata.org/wiki/Q1502246) | biological parent | parent directly biologically related to their biological child |  |
| [Q1503423](https://www.wikidata.org/wiki/Q1503423) | quasigroup | magma satisfying the Latin square property | [Quasigroup](https://en.wikipedia.org/wiki/Quasigroup) |
| [Q1520223](https://www.wikidata.org/wiki/Q1520223) | constitutional republic | type of republic that operates under a system of separation of powers |  |
| [Q1531349](https://www.wikidata.org/wiki/Q1531349) | outline | list arranged to show hierarchical relationships | [Outline (list)](https://en.wikipedia.org/wiki/Outline_%28list%29) |
| [Q1549152](https://www.wikidata.org/wiki/Q1549152) | public institution | an organization for public use |  |
| [Q1549591](https://www.wikidata.org/wiki/Q1549591) | big city | city with a population of between 100,000 and 250,000 |  |
| [Q1554231](https://www.wikidata.org/wiki/Q1554231) | resource | source or supply from which benefit is produced | [Resource](https://en.wikipedia.org/wiki/Resource) |
| [Q1575634](https://www.wikidata.org/wiki/Q1575634) | concrete category | category equipped with a faithful functor to the category of sets | [Concrete category](https://en.wikipedia.org/wiki/Concrete_category) |
| [Q1609475](https://www.wikidata.org/wiki/Q1609475) | Herbrand structure | structure over a vocabulary defined solely by syntactical properties | [Herbrand structure](https://en.wikipedia.org/wiki/Herbrand_structure) |
| [Q1620908](https://www.wikidata.org/wiki/Q1620908) | historical region | geographic or cultural region which existed in the past, that may or may not exist anymore | [Historical region](https://en.wikipedia.org/wiki/Historical_region) |
| [Q1621273](https://www.wikidata.org/wiki/Q1621273) | particle | small localized object in physical sciences | [Particle](https://en.wikipedia.org/wiki/Particle) |
| [Q1625040](https://www.wikidata.org/wiki/Q1625040) | injective object | object 𝑋 in an abelian category such that hom(–,𝑋) is an exact functor to the opposite category of the category of abelian groups | [Injective object](https://en.wikipedia.org/wiki/Injective_object) |
| [Q1626409](https://www.wikidata.org/wiki/Q1626409) | homotopy equivalence | equivalence relation on topological spaces | [Homotopy equivalence](https://en.wikipedia.org/wiki/Homotopy_equivalence) |
| [Q1630279](https://www.wikidata.org/wiki/Q1630279) | guideline | instruction as to the preferred, recommended, or approved way of performing a task, publication type | [Guideline](https://en.wikipedia.org/wiki/Guideline) |
| [Q1633079](https://www.wikidata.org/wiki/Q1633079) | pushout | category-theoretic colimit of a diagram of the form 𝑋←𝑍→𝑌 | [Pushout (category theory)](https://en.wikipedia.org/wiki/Pushout_%28category_theory%29) |
| [Q1637706](https://www.wikidata.org/wiki/Q1637706) | million city | city with a population of more than 1,000,000 |  |
| [Q1639378](https://www.wikidata.org/wiki/Q1639378) | social system | patterned series of interrelationships existing between individuals, groups, and institutions | [Social system](https://en.wikipedia.org/wiki/Social_system) |
| [Q1650915](https://www.wikidata.org/wiki/Q1650915) | researcher | person who engages in research, professionally or otherwise. If a more specific occupation is known, use that instead | [Researcher](https://en.wikipedia.org/wiki/Researcher) |
| [Q1656682](https://www.wikidata.org/wiki/Q1656682) | planned event | temporary and scheduled happening, like a conference, festival, competition or similar |  |
| [Q1657198](https://www.wikidata.org/wiki/Q1657198) | set function | function whose domain is a collection of sets | [Set function](https://en.wikipedia.org/wiki/Set_function) |
| [Q1662611](https://www.wikidata.org/wiki/Q1662611) | IT system | all systems consisting of a combination of hardware, software and networks that can process data |  |
| [Q1667921](https://www.wikidata.org/wiki/Q1667921) | novel series | set of novels that should be read in order |  |
| [Q1668024](https://www.wikidata.org/wiki/Q1668024) | service on Internet | technical ability afforded by the Internet |  |
| [Q1714118](https://www.wikidata.org/wiki/Q1714118) | online publication | work manifested on the Internet |  |
| [Q1723418](https://www.wikidata.org/wiki/Q1723418) | Kan extension | Category theory constructs | [Kan extension](https://en.wikipedia.org/wiki/Kan_extension) |
| [Q1724915](https://www.wikidata.org/wiki/Q1724915) | use | use of a resource to perform a task |  |
| [Q1725874](https://www.wikidata.org/wiki/Q1725874) | cartesian closed category | Type of category in category theory | [Cartesian closed category](https://en.wikipedia.org/wiki/Cartesian_closed_category) |
| [Q1729838](https://www.wikidata.org/wiki/Q1729838) | pseudo magma | algebraic structure |  |
| [Q1747121](https://www.wikidata.org/wiki/Q1747121) | flaw | characteristic of an item that deviates from the ideal or perfect form |  |
| [Q1751819](https://www.wikidata.org/wiki/Q1751819) | RDF Schema | schema for knowledge representation | [RDF Schema](https://en.wikipedia.org/wiki/RDF_Schema) |
| [Q1754533](https://www.wikidata.org/wiki/Q1754533) | source text | text (sometimes oral) from which information or ideas are derived. In translation, a source text is the original text that is to be translated into another language | [Source text](https://en.wikipedia.org/wiki/Source_text) |
| [Q1756942](https://www.wikidata.org/wiki/Q1756942) | partial function | function whose actual domain of definition may be smaller than its input set | [Partial function](https://en.wikipedia.org/wiki/Partial_function) |
| [Q1757074](https://www.wikidata.org/wiki/Q1757074) | root node | chosen vertex in a graph | [Root node](https://en.wikipedia.org/wiki/Root_node) |
| [Q1759104](https://www.wikidata.org/wiki/Q1759104) | warning | signal used to warn of danger |  |
| [Q1767348](https://www.wikidata.org/wiki/Q1767348) | legal kinship | type of familial relationship which is legal in nature |  |
| [Q1777803](https://www.wikidata.org/wiki/Q1777803) | coalgebra | vector space V equipped with a linear map V → V ⊗ V | [Coalgebra](https://en.wikipedia.org/wiki/Coalgebra) |
| [Q1780005](https://www.wikidata.org/wiki/Q1780005) | comma category | mathematics construct | [Comma category](https://en.wikipedia.org/wiki/Comma_category) |
| [Q1781706](https://www.wikidata.org/wiki/Q1781706) | conjunctive query | restricted form of first-order query using the logical conjunction operator | [Conjunctive query](https://en.wikipedia.org/wiki/Conjunctive_query) |
| [Q1789452](https://www.wikidata.org/wiki/Q1789452) | criterion | a feature used for distinguishing and selecting entities of interest |  |
| [Q1792379](https://www.wikidata.org/wiki/Q1792379) | art genre | form of art in terms of a medium, format or theme |  |
| [Q1799072](https://www.wikidata.org/wiki/Q1799072) | method | planned path to reaching an objective |  |
| [Q1799794](https://www.wikidata.org/wiki/Q1799794) | administrative territorial entity of a specific level | type of administrative territorial entity |  |
| [Q1801244](https://www.wikidata.org/wiki/Q1801244) | zero-dimensional space | topological space that has small inductive dimension zero | [Zero-dimensional space](https://en.wikipedia.org/wiki/Zero-dimensional_space) |
| [Q1807498](https://www.wikidata.org/wiki/Q1807498) | social position | position of an individual in a given society and culture | [Social position](https://en.wikipedia.org/wiki/Social_position) |
| [Q1851710](https://www.wikidata.org/wiki/Q1851710) | structure (model theory) | set together with an interpretation of a given first-order language | [Structure (mathematical logic)](https://en.wikipedia.org/wiki/Structure_%28mathematical_logic%29) |
| [Q1879813](https://www.wikidata.org/wiki/Q1879813) | solution | mathematical object which is a solution for a mathematical problem |  |
| [Q1896989](https://www.wikidata.org/wiki/Q1896989) | subject of international law |  | [Subject of international law](https://en.wikipedia.org/wiki/Subject_of_international_law) |
| [Q1900326](https://www.wikidata.org/wiki/Q1900326) | network | system of objects that are connected together to exchange something (e.g. objects, materials or information) |  |
| [Q1901835](https://www.wikidata.org/wiki/Q1901835) | seat of government | building, complex of buildings or city from which a government exercises its authority | [Seat of government](https://en.wikipedia.org/wiki/Seat_of_government) |
| [Q1907114](https://www.wikidata.org/wiki/Q1907114) | metropolitan area | administrative unit of a dense urban core and its satellite cities | [Metropolitan area](https://en.wikipedia.org/wiki/Metropolitan_area) |
| [Q1914017](https://www.wikidata.org/wiki/Q1914017) | knowledge worker | worker whose main capital is knowledge | [Knowledge worker](https://en.wikipedia.org/wiki/Knowledge_worker) |
| [Q1914636](https://www.wikidata.org/wiki/Q1914636) | activity | series of actions done by an agent which results in an external change of state |  |
| [Q1920219](https://www.wikidata.org/wiki/Q1920219) | social issue | problem that influences a considerable number of individuals within a society | [Social issue](https://en.wikipedia.org/wiki/Social_issue) |
| [Q1936384](https://www.wikidata.org/wiki/Q1936384) | branch of mathematics | grouping by subject of mathematics | [Areas of mathematics](https://en.wikipedia.org/wiki/Areas_of_mathematics) |
| [Q1941921](https://www.wikidata.org/wiki/Q1941921) | modeling language | artificial language that can be used to express information or knowledge or systems in a structure that is defined by a consistent set of rules | [Modeling language](https://en.wikipedia.org/wiki/Modeling_language) |
| [Q1945014](https://www.wikidata.org/wiki/Q1945014) | monoidal category | category admitting tensor products | [Monoidal category](https://en.wikipedia.org/wiki/Monoidal_category) |
| [Q1945067](https://www.wikidata.org/wiki/Q1945067) | monomorphism | left-cancellative morphism | [Monomorphism](https://en.wikipedia.org/wiki/Monomorphism) |
| [Q1948412](https://www.wikidata.org/wiki/Q1948412) | morphism | map (arrow) between two objects of a category | [Morphism](https://en.wikipedia.org/wiki/Morphism) |
| [Q1964995](https://www.wikidata.org/wiki/Q1964995) | set operation | operation in set theory |  |
| [Q1968442](https://www.wikidata.org/wiki/Q1968442) | donor | person who donates, usually money | [Donor](https://en.wikipedia.org/wiki/Donor) |
| [Q1969448](https://www.wikidata.org/wiki/Q1969448) | term | word, compound word, or expression that in specific contexts is given specific meanings | [Term (language)](https://en.wikipedia.org/wiki/Term_%28language%29) |
| [Q1970309](https://www.wikidata.org/wiki/Q1970309) | natural object | naturally occurring object in a natural state, without modification by human effort |  |
| [Q1979154](https://www.wikidata.org/wiki/Q1979154) | model | representation of an entity, either physical or conceptual | [Model](https://en.wikipedia.org/wiki/Model) |
| [Q1980247](https://www.wikidata.org/wiki/Q1980247) | chapter | section of a work, most commonly a book | [Chapter (books)](https://en.wikipedia.org/wiki/Chapter_%28books%29) |
| [Q1985727](https://www.wikidata.org/wiki/Q1985727) | proleptic Gregorian calendar | extension of the Gregorian calendar before its introduction | [Proleptic Gregorian calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar) |
| [Q1985786](https://www.wikidata.org/wiki/Q1985786) | proleptic Julian calendar | extension of the regular Julian calendar | [Proleptic Julian calendar](https://en.wikipedia.org/wiki/Proleptic_Julian_calendar) |
| [Q1993334](https://www.wikidata.org/wiki/Q1993334) | interpreted language | programming language for which most of its implementations execute instructions directly | [Interpreted language](https://en.wikipedia.org/wiki/Interpreted_language) |
| [Q2007878](https://www.wikidata.org/wiki/Q2007878) | functor category | category containing functors with natural transformations as morphisms | [Functor category](https://en.wikipedia.org/wiki/Functor_category) |
| [Q2030545](https://www.wikidata.org/wiki/Q2030545) | algebra over a ring | module over a ring whose multiplication is bilinear | [Algebra (ring theory)](https://en.wikipedia.org/wiki/Algebra_%28ring_theory%29) |
| [Q2057971](https://www.wikidata.org/wiki/Q2057971) | health problem | condition negatively affecting the health of an organism |  |
| [Q2067937](https://www.wikidata.org/wiki/Q2067937) | tree structure | way of representing the hierarchical nature of a structure in a graphical form | [Tree structure](https://en.wikipedia.org/wiki/Tree_structure) |
| [Q2083958](https://www.wikidata.org/wiki/Q2083958) | pattern | discernible regularity in an entity or set of entities | [Pattern](https://en.wikipedia.org/wiki/Pattern) |
| [Q2085518](https://www.wikidata.org/wiki/Q2085518) | format | arrangement of data for presentation |  |
| [Q2101564](https://www.wikidata.org/wiki/Q2101564) | specification | explicit implementation of requirements to be satisfied by a material, design, product, or service | [Specification (technical standard)](https://en.wikipedia.org/wiki/Specification_%28technical_standard%29) |
| [Q2101636](https://www.wikidata.org/wiki/Q2101636) | political power | ability to influence or direct the actions, beliefs, or conduct of actors | [Political power](https://en.wikipedia.org/wiki/Political_power) |
| [Q2112502](https://www.wikidata.org/wiki/Q2112502) | projective object | object 𝑃 in an abelian category such that hom(𝑃,–) is an exact functor to the category of abelian groups | [Projective object](https://en.wikipedia.org/wiki/Projective_object) |
| [Q2135465](https://www.wikidata.org/wiki/Q2135465) | legal term or legal concept | lexeme with a specific meaning in jurisprudence | [Legal term](https://en.wikipedia.org/wiki/Legal_term) |
| [Q2141565](https://www.wikidata.org/wiki/Q2141565) | situation | position with respect to conditions, circumstances and contexts |  |
| [Q2141963](https://www.wikidata.org/wiki/Q2141963) | retract | continuous mapping from a topological space into a subspace that preserves the position of all points in that subspace | [Retraction (topology)](https://en.wikipedia.org/wiki/Retraction_%28topology%29) |
| [Q2143621](https://www.wikidata.org/wiki/Q2143621) | topos | category admitting all finite limits and power objects, that can be viewed as either as a mathematical universe (replacing the category of sets) or as a generalized space (considered as a generalization of the category of sheaves on a space) | [Topos](https://en.wikipedia.org/wiki/Topos) |
| [Q2145290](https://www.wikidata.org/wiki/Q2145290) | mental representation | hypothetical internal cognitive symbol that represents external reality | [Mental representation](https://en.wikipedia.org/wiki/Mental_representation) |
| [Q2146022](https://www.wikidata.org/wiki/Q2146022) | ring of integers modulo n |  | [Ring of integers modulo n](https://en.wikipedia.org/wiki/Ring_of_integers_modulo_n) |
| [Q2150504](https://www.wikidata.org/wiki/Q2150504) | signal | symbolic sign or indicating device made to give notice of some occurrence, command or danger |  |
| [Q2165111](https://www.wikidata.org/wiki/Q2165111) | alternative algebra | abstract algebra with alternative multiplication | [Alternative algebra](https://en.wikipedia.org/wiki/Alternative_algebra) |
| [Q2166096](https://www.wikidata.org/wiki/Q2166096) | theoretical philosophy | branch of philosophy | [Theoretical philosophy](https://en.wikipedia.org/wiki/Theoretical_philosophy) |
| [Q2169973](https://www.wikidata.org/wiki/Q2169973) | service provider | organization that provides organizations with services | [Service provider](https://en.wikipedia.org/wiki/Service_provider) |
| [Q2188189](https://www.wikidata.org/wiki/Q2188189) | musical work | generic term for any work of art related to music, i.e. songs, compositions, groups of compositions, sheet music, melodies, albums, musical films, etc. | [Musical work](https://en.wikipedia.org/wiki/Musical_work) |
| [Q2198779](https://www.wikidata.org/wiki/Q2198779) | unit | entity regarded or used as an elementary structural or functional constituent to measure, analyse or describe another entity |  |
| [Q2217301](https://www.wikidata.org/wiki/Q2217301) | serial | publication in any medium issued under the same title in a succession of discrete parts, usually numbered (or dated) and appearing at regular or irregular intervals with no predetermined conclusion | [Serial (publishing)](https://en.wikipedia.org/wiki/Serial_%28publishing%29) |
| [Q2221906](https://www.wikidata.org/wiki/Q2221906) | geographic location | point, line or area on or near Earth | [Location](https://en.wikipedia.org/wiki/Location) |
| [Q2240381](https://www.wikidata.org/wiki/Q2240381) | fashion capital | city that influences fashion trends | [Fashion capital](https://en.wikipedia.org/wiki/Fashion_capital) |
| [Q2243424](https://www.wikidata.org/wiki/Q2243424) | idempotent element | element x of a ring such that x² = x | [Idempotent (ring theory)](https://en.wikipedia.org/wiki/Idempotent_%28ring_theory%29) |
| [Q2250224](https://www.wikidata.org/wiki/Q2250224) | individual person |  |  |
| [Q2267705](https://www.wikidata.org/wiki/Q2267705) | field of study | field of study leading to a specific degree |  |
| [Q2268906](https://www.wikidata.org/wiki/Q2268906) | semantic relation | relation between two elements with meaning such as hypernymy and holonymy |  |
| [Q2269249](https://www.wikidata.org/wiki/Q2269249) | semiprime ideal | generalizations of prime ideals | [Semiprime ideal](https://en.wikipedia.org/wiki/Semiprime_ideal) |
| [Q2288360](https://www.wikidata.org/wiki/Q2288360) | SKOS | W3C recommendation designed for representation of thesauri, classification schemes, taxonomies, subject-heading systems, or other structured controlled vocabularies | [Simple Knowledge Organization System](https://en.wikipedia.org/wiki/Simple_Knowledge_Organization_System) |
| [Q2298831](https://www.wikidata.org/wiki/Q2298831) | asymmetric relation | binary relation such that if A is related to B then B is not related to A | [Asymmetric relation](https://en.wikipedia.org/wiki/Asymmetric_relation) |
| [Q2303697](https://www.wikidata.org/wiki/Q2303697) | sorting | action of arranging objects into order | [Sorting](https://en.wikipedia.org/wiki/Sorting) |
| [Q2305441](https://www.wikidata.org/wiki/Q2305441) | social process | way of interaction between individuals and groups |  |
| [Q2324993](https://www.wikidata.org/wiki/Q2324993) | state power | type of political power | [State power](https://en.wikipedia.org/wiki/State_power) |
| [Q2326800](https://www.wikidata.org/wiki/Q2326800) | simple ring | nonzero ring that has no two-sided ideal besides the zero ideal and itself | [Simple ring](https://en.wikipedia.org/wiki/Simple_ring) |
| [Q2353731](https://www.wikidata.org/wiki/Q2353731) | upbringing | type of education |  |
| [Q2354159](https://www.wikidata.org/wiki/Q2354159) | finite ring | abstract ring with finite number of elements | [Finite ring](https://en.wikipedia.org/wiki/Finite_ring) |
| [Q2360980](https://www.wikidata.org/wiki/Q2360980) | unit of amount | class of units for determining the amount of a good by counting |  |
| [Q2362924](https://www.wikidata.org/wiki/Q2362924) | complete lattice | partially ordered set in which all subsets have both a supremum and infimum | [Complete lattice](https://en.wikipedia.org/wiki/Complete_lattice) |
| [Q2363730](https://www.wikidata.org/wiki/Q2363730) | distributive lattice | lattice in which the operations of join and meet distribute over each other | [Distributive lattice](https://en.wikipedia.org/wiki/Distributive_lattice) |
| [Q2374463](https://www.wikidata.org/wiki/Q2374463) | data science | field of study to extract insights from data | [Data science](https://en.wikipedia.org/wiki/Data_science) |
| [Q2374489](https://www.wikidata.org/wiki/Q2374489) | grammeme | value of a grammatical category | [Grammeme](https://en.wikipedia.org/wiki/Grammeme) |
| [Q2385804](https://www.wikidata.org/wiki/Q2385804) | educational institution | institution that provides education | [Educational institution](https://en.wikipedia.org/wiki/Educational_institution) |
| [Q2393187](https://www.wikidata.org/wiki/Q2393187) | molecular entity | any constitutionally or isotopically distinct atom, molecule, ion, ion pair, radical, radical ion, complex, conformer, etc., identifiable as a separately distinguishable entity | [Molecular entity](https://en.wikipedia.org/wiki/Molecular_entity) |
| [Q2423459](https://www.wikidata.org/wiki/Q2423459) | military deployment | movement of armed forces and their logistical support infrastructure around the world | [Military deployment](https://en.wikipedia.org/wiki/Military_deployment) |
| [Q2424752](https://www.wikidata.org/wiki/Q2424752) | product | anything that can be offered to a market | [Product (business)](https://en.wikipedia.org/wiki/Product_%28business%29) |
| [Q2427941](https://www.wikidata.org/wiki/Q2427941) | foster parent | parent who raises someone who is not their natural or adoptive child |  |
| [Q2431196](https://www.wikidata.org/wiki/Q2431196) | audiovisual work | creative work possessing both a sound and a visual component |  |
| [Q2438541](https://www.wikidata.org/wiki/Q2438541) | manner of death | type of death (natural / not natural) | [Manner of death](https://en.wikipedia.org/wiki/Manner_of_death) |
| [Q2444982](https://www.wikidata.org/wiki/Q2444982) | Noetherian module | module without any strictly ascending sequence of submodules | [Noetherian module](https://en.wikipedia.org/wiki/Noetherian_module) |
| [Q2465832](https://www.wikidata.org/wiki/Q2465832) | branch of science | field of scientific study | [Branches of science](https://en.wikipedia.org/wiki/Branches_of_science) |
| [Q2479726](https://www.wikidata.org/wiki/Q2479726) | graph data structure | abstract data type in computer science | [Graph (abstract data type)](https://en.wikipedia.org/wiki/Graph_%28abstract_data_type%29) |
| [Q2515887](https://www.wikidata.org/wiki/Q2515887) | pattern of behavior | type of behavior |  |
| [Q2547089](https://www.wikidata.org/wiki/Q2547089) | subobject | object within another object of the same category | [Subobject](https://en.wikipedia.org/wiki/Subobject) |
| [Q2574811](https://www.wikidata.org/wiki/Q2574811) | cause | entity which forms causality for an event |  |
| [Q2605444](https://www.wikidata.org/wiki/Q2605444) | society form |  |  |
| [Q2617970](https://www.wikidata.org/wiki/Q2617970) | pentalogy | compound literary or narrative work that is divided into five | [Pentalogy](https://en.wikipedia.org/wiki/Pentalogy) |
| [Q2623243](https://www.wikidata.org/wiki/Q2623243) | conceptual model | representation of a system, made of the composition of concepts | [Conceptual model](https://en.wikipedia.org/wiki/Conceptual_model) |
| [Q2646117](https://www.wikidata.org/wiki/Q2646117) | forgetful functor | drops some or all of the input's structure or properties | [Forgetful functor](https://en.wikipedia.org/wiki/Forgetful_functor) |
| [Q2648051](https://www.wikidata.org/wiki/Q2648051) | obligation | legal or moral requirement to take a certain course of action | [Obligation](https://en.wikipedia.org/wiki/Obligation) |
| [Q2659904](https://www.wikidata.org/wiki/Q2659904) | government organization | organization administrated by a government authority or agency | [Government organization](https://en.wikipedia.org/wiki/Government_organization) |
| [Q2661442](https://www.wikidata.org/wiki/Q2661442) | W3C Recommendation | class of technical specifications by W3C |  |
| [Q2668072](https://www.wikidata.org/wiki/Q2668072) | collection | set of purposely gathered physical or digital objects with some common characteristics | [Collection (museum)](https://en.wikipedia.org/wiki/Collection_%28museum%29) |
| [Q2712963](https://www.wikidata.org/wiki/Q2712963) | abstract noun | noun, with which somewhat non-representational is designated | [Abstract noun](https://en.wikipedia.org/wiki/Abstract_noun) |
| [Q2742711](https://www.wikidata.org/wiki/Q2742711) | graph distance | in graph theory, the minimum number of edges in a path connecting two vertices | [Distance (graph theory)](https://en.wikipedia.org/wiki/Distance_%28graph_theory%29) |
| [Q2752458](https://www.wikidata.org/wiki/Q2752458) | administrative type | general umbrella term for the way in which a community is run |  |
| [Q2785361](https://www.wikidata.org/wiki/Q2785361) | monoid object | monoid in certain category-theoretic category | [Monoid (category theory)](https://en.wikipedia.org/wiki/Monoid_%28category_theory%29) |
| [Q2835924](https://www.wikidata.org/wiki/Q2835924) | octonion algebra | 8-dimensional composition algebra over a field | [Octonion algebra](https://en.wikipedia.org/wiki/Octonion_algebra) |
| [Q2835957](https://www.wikidata.org/wiki/Q2835957) | composition algebra | not necessarily associative algebra | [Composition algebra](https://en.wikipedia.org/wiki/Composition_algebra) |
| [Q2851410](https://www.wikidata.org/wiki/Q2851410) | coherent ring | ring in which every finitely generated left ideal is finitely presented | [Coherent ring](https://en.wikipedia.org/wiki/Coherent_ring) |
| [Q2897903](https://www.wikidata.org/wiki/Q2897903) | goods and services | outcome of human efforts to meet the wants and needs of people | [Goods and services](https://en.wikipedia.org/wiki/Goods_and_services) |
| [Q2901852](https://www.wikidata.org/wiki/Q2901852) | carbon compound | any chemical compound having at least one carbon atom | [Carbon compounds](https://en.wikipedia.org/wiki/Carbon_compounds) |
| [Q2903989](https://www.wikidata.org/wiki/Q2903989) | class hierarchy | classification of objects in programming | [Class hierarchy](https://en.wikipedia.org/wiki/Class_hierarchy) |
| [Q2905043](https://www.wikidata.org/wiki/Q2905043) | principal ideal ring | ring in which every ideal is principal | [Principal ideal ring](https://en.wikipedia.org/wiki/Principal_ideal_ring) |
| [Q2912517](https://www.wikidata.org/wiki/Q2912517) | value | notion in mathematics | [Value (mathematics)](https://en.wikipedia.org/wiki/Value_%28mathematics%29) |
| [Q2919100](https://www.wikidata.org/wiki/Q2919100) | Artinian module | module which satisfies the descending chain condition on submodules | [Artinian module](https://en.wikipedia.org/wiki/Artinian_module) |
| [Q2920613](https://www.wikidata.org/wiki/Q2920613) | shared parenting | child custody arrangement | [Shared parenting](https://en.wikipedia.org/wiki/Shared_parenting) |
| [Q2923525](https://www.wikidata.org/wiki/Q2923525) | massive particle | particle having real positive rest mass | [Massive particle](https://en.wikipedia.org/wiki/Massive_particle) |
| [Q2943034](https://www.wikidata.org/wiki/Q2943034) | braided monoidal category | monoidal category with a commutativity constraint that need not be symmetric | [Braided monoidal category](https://en.wikipedia.org/wiki/Braided_monoidal_category) |
| [Q2944660](https://www.wikidata.org/wiki/Q2944660) | lexical item | basic unit of a language’s lexicon | [Lexical item](https://en.wikipedia.org/wiki/Lexical_item) |
| [Q2976602](https://www.wikidata.org/wiki/Q2976602) | industry classification scheme | type of economic taxonomy | [Industry classification](https://en.wikipedia.org/wiki/Industry_classification) |
| [Q2990593](https://www.wikidata.org/wiki/Q2990593) | animal behavior | internally coordinated responses (actions or inactions) of animals (individuals or groups) to internal or external stimuli, via a mechanism that involves nervous system activity | [Animal behaviour](https://en.wikipedia.org/wiki/Animal_behaviour) |
| [Q2995644](https://www.wikidata.org/wiki/Q2995644) | result | final consequence or product of a sequence of actions or events | [Result](https://en.wikipedia.org/wiki/Result) |
| [Q2996394](https://www.wikidata.org/wiki/Q2996394) | biological process | process specifically pertinent to the functioning of integrated living units | [Biological process](https://en.wikipedia.org/wiki/Biological_process) |
| [Q2996729](https://www.wikidata.org/wiki/Q2996729) | coparenting | type of parenting | [Coparenting](https://en.wikipedia.org/wiki/Coparenting) |
| [Q2997817](https://www.wikidata.org/wiki/Q2997817) | perfect field | a field that is either of characteristic 0, or of positive characteristic p such that every element admits a p-th root | [Perfect field](https://en.wikipedia.org/wiki/Perfect_field) |
| [Q3022118](https://www.wikidata.org/wiki/Q3022118) | inverse semigroup | regular semigroup in which every element has a unique inverse | [Inverse semigroup](https://en.wikipedia.org/wiki/Inverse_semigroup) |
| [Q3022119](https://www.wikidata.org/wiki/Q3022119) | regular semigroup | semigroup such that, for every element x, there exists another element y such that xyx=x | [Regular semigroup](https://en.wikipedia.org/wiki/Regular_semigroup) |
| [Q3024240](https://www.wikidata.org/wiki/Q3024240) | historical country | country, state or territory that once existed | [Historical country](https://en.wikipedia.org/wiki/Historical_country) |
| [Q3052382](https://www.wikidata.org/wiki/Q3052382) | fonds | aggregation of records, documents, or works originating from the same creator | [Fonds](https://en.wikipedia.org/wiki/Fonds) |
| [Q3054922](https://www.wikidata.org/wiki/Q3054922) | totally ordered set | set paired with a total order | [Totally ordered set](https://en.wikipedia.org/wiki/Totally_ordered_set) |
| [Q3059449](https://www.wikidata.org/wiki/Q3059449) | Nephrozoa | proposed clade of animals | [Nephrozoa](https://en.wikipedia.org/wiki/Nephrozoa) |
| [Q3084232](https://www.wikidata.org/wiki/Q3084232) | polypeptide | long, continuous, and unbranched peptide chain |  |
| [Q3088151](https://www.wikidata.org/wiki/Q3088151) | transitive reduction | minimal graph with the same reachability relation as a given graph | [Transitive reduction](https://en.wikipedia.org/wiki/Transitive_reduction) |
| [Q3181395](https://www.wikidata.org/wiki/Q3181395) | information processor | system (be it electrical, mechanical, biological) which takes information (a sequence of enumerated symbols, states) in one form and processes (transforms, converts) it into another form, e.g. to statistics, by an algorithmic process |  |
| [Q3182649](https://www.wikidata.org/wiki/Q3182649) | separation | process of separating one entity to form others; often: separation within an organization that leads to the formation of an independent organisation |  |
| [Q3249551](https://www.wikidata.org/wiki/Q3249551) | process | series of events which occur over an extended period of time | [Process (science)](https://en.wikipedia.org/wiki/Process_%28science%29) |
| [Q3257686](https://www.wikidata.org/wiki/Q3257686) | locality | place of human settlement |  |
| [Q3257782](https://www.wikidata.org/wiki/Q3257782) | locution | language functional unit |  |
| [Q3266850](https://www.wikidata.org/wiki/Q3266850) | commune | administrative entity in different countries | [Commune (administrative division)](https://en.wikipedia.org/wiki/Commune_%28administrative_division%29) |
| [Q3268571](https://www.wikidata.org/wiki/Q3268571) | administrative territorial entity of a single country | class of all the administrative division types used by a given country administration |  |
| [Q3269789](https://www.wikidata.org/wiki/Q3269789) | unital ring | another name of ring | [Unital ring](https://en.wikipedia.org/wiki/Unital_ring) |
| [Q3305213](https://www.wikidata.org/wiki/Q3305213) | painting | visual artwork, surface artistically covered with paint | [Painting (object)](https://en.wikipedia.org/wiki/Painting_%28object%29) |
| [Q3306762](https://www.wikidata.org/wiki/Q3306762) | data validation | technical process | [Data validation](https://en.wikipedia.org/wiki/Data_validation) |
| [Q3307145](https://www.wikidata.org/wiki/Q3307145) | finite measure | measure that always takes on finite values | [Finite measure](https://en.wikipedia.org/wiki/Finite_measure) |
| [Q3365007](https://www.wikidata.org/wiki/Q3365007) | parenthood | the function of being a parent in its legal, political, socio-economic, cultural and institutional aspects |  |
| [Q3366856](https://www.wikidata.org/wiki/Q3366856) | composite particle | quantum particle that is itself a system of other quantum particles bound by strong, weak or electromagnetic interaction |  |
| [Q3400985](https://www.wikidata.org/wiki/Q3400985) | academic | person who works as a teacher or researcher at a university or other higher education institution |  |
| [Q3413373](https://www.wikidata.org/wiki/Q3413373) | quasi-bialgebra | mathematical concept | [Quasi-bialgebra](https://en.wikipedia.org/wiki/Quasi-bialgebra) |
| [Q3427877](https://www.wikidata.org/wiki/Q3427877) | web resource | resource accessible from the World Wide Web and has a Uniform Resource Identifier. Can be resource of different file formats, accessible by a specific protocol, etc. | [Web resource](https://en.wikipedia.org/wiki/Web_resource) |
| [Q3435924](https://www.wikidata.org/wiki/Q3435924) | computational problem | problem of finding an effective algorithm which solves a given problem | [Computational problem](https://en.wikipedia.org/wiki/Computational_problem) |
| [Q3505845](https://www.wikidata.org/wiki/Q3505845) | state | abstract term that denotes the presence of stable values of a set of variables of an object |  |
| [Q3511132](https://www.wikidata.org/wiki/Q3511132) | series | term in archival and library science; collection of records grouped as a result of their original function, use, or other relationship to one another |  |
| [Q3523102](https://www.wikidata.org/wiki/Q3523102) | source of information | source of information for somebody, i.e. anything that might inform a person about something or provide knowledge about it | [Source of information](https://en.wikipedia.org/wiki/Source_of_information) |
| [Q3532117](https://www.wikidata.org/wiki/Q3532117) | Alexandrov topology | topology in which the intersection of any family of open sets is open | [Alexandrov topology](https://en.wikipedia.org/wiki/Alexandrov_topology) |
| [Q3533467](https://www.wikidata.org/wiki/Q3533467) | group action | in sociology, a situation in which a number of agents take action simultaneously in order to achieve a common goal | [Group action (sociology)](https://en.wikipedia.org/wiki/Group_action_%28sociology%29) |
| [Q3537603](https://www.wikidata.org/wiki/Q3537603) | transgression | violation of a commitment, law, norm or other rule |  |
| [Q3539534](https://www.wikidata.org/wiki/Q3539534) | semantic triple | atomic data entity in the Resource Description Framework (RDF) data model; set of three entities that codifies a statement about semantic data in the form of subject–predicate–object expressions | [Semantic triple](https://en.wikipedia.org/wiki/Semantic_triple) |
| [Q3622002](https://www.wikidata.org/wiki/Q3622002) | geographical area | type of geographic region | [Geographical area](https://en.wikipedia.org/wiki/Geographical_area) |
| [Q3622126](https://www.wikidata.org/wiki/Q3622126) | conceptual system | system composed of non-physical objects, i.e. ideas or concepts | [Conceptual system](https://en.wikipedia.org/wiki/Conceptual_system) |
| [Q3624078](https://www.wikidata.org/wiki/Q3624078) | sovereign state | state that has the highest authority over a territory | [Sovereign state](https://en.wikipedia.org/wiki/Sovereign_state) |
| [Q3685323](https://www.wikidata.org/wiki/Q3685323) | nitrogen compound | any chemical compound having at least one nitrogen atom | [Nitrogen compounds](https://en.wikipedia.org/wiki/Nitrogen_compounds) |
| [Q3695082](https://www.wikidata.org/wiki/Q3695082) | sign | semiotic concept; object, quality, event, or entity whose presence or occurrence indicates the probable presence or occurrence of something else; includes words, punctuation, expressions, gestures, notices, road signs, symbols, pictures, etc. | [Sign](https://en.wikipedia.org/wiki/Sign) |
| [Q3736439](https://www.wikidata.org/wiki/Q3736439) | duck | common name for many species in the bird family Anatidae | [Duck](https://en.wikipedia.org/wiki/Duck) |
| [Q3737844](https://www.wikidata.org/wiki/Q3737844) | binary function | function that takes two inputs | [Binary function](https://en.wikipedia.org/wiki/Binary_function) |
| [Q3753945](https://www.wikidata.org/wiki/Q3753945) | closure of a relation |  | [Closure of a relation](https://en.wikipedia.org/wiki/Closure_of_a_relation) |
| [Q3778211](https://www.wikidata.org/wiki/Q3778211) | legal person | any entity that is recognised as having privileges and obligations in law | [Legal person](https://en.wikipedia.org/wiki/Legal_person) |
| [Q3836720](https://www.wikidata.org/wiki/Q3836720) | loop | algebraic structure, quasigroup with an identity element | [Loop (algebra)](https://en.wikipedia.org/wiki/Loop_%28algebra%29) |
| [Q3839507](https://www.wikidata.org/wiki/Q3839507) | functional programming language | programming language that uses functional programming principles | [Functional programming language](https://en.wikipedia.org/wiki/Functional_programming_language) |
| [Q3882785](https://www.wikidata.org/wiki/Q3882785) | upper ontology | ontology applicable across domains of knowledge | [Upper ontology](https://en.wikipedia.org/wiki/Upper_ontology) |
| [Q3884033](https://www.wikidata.org/wiki/Q3884033) | mathematical operation | mathematical procedure which produces a result from one or more input values | [Operation (mathematics)](https://en.wikipedia.org/wiki/Operation_%28mathematics%29) |
| [Q3893614](https://www.wikidata.org/wiki/Q3893614) | definable real number | real number uniquely specified by description | [Definable real number](https://en.wikipedia.org/wiki/Definable_real_number) |
| [Q3924032](https://www.wikidata.org/wiki/Q3924032) | mathematical property | mathematical concept | [Property (mathematics)](https://en.wikipedia.org/wiki/Property_%28mathematics%29) |
| [Q3927329](https://www.wikidata.org/wiki/Q3927329) | 4-tuple | tuple of specific length (tuple length n=4) | [4-tuple](https://en.wikipedia.org/wiki/4-tuple) |
| [Q3929429](https://www.wikidata.org/wiki/Q3929429) | semantic reasoner | software able to infer logical consequences from a set of asserted facts or axioms | [Semantic reasoner](https://en.wikipedia.org/wiki/Semantic_reasoner) |
| [Q3958441](https://www.wikidata.org/wiki/Q3958441) | economic sector | conceptual grouping of economic activities | [Economic sector](https://en.wikipedia.org/wiki/Economic_sector) |
| [Q3965271](https://www.wikidata.org/wiki/Q3965271) | subclass | class whose elements are all elements of a given other class | [Subclass (set theory)](https://en.wikipedia.org/wiki/Subclass_%28set_theory%29) |
| [Q3966112](https://www.wikidata.org/wiki/Q3966112) | quotient set | set formed by the equivalence classes on a set under a given equivalence relation | [Quotient set](https://en.wikipedia.org/wiki/Quotient_set) |
| [Q4025884](https://www.wikidata.org/wiki/Q4025884) | concrete number | number associated with the things being counted | [Concrete number](https://en.wikipedia.org/wiki/Concrete_number) |
| [Q4026292](https://www.wikidata.org/wiki/Q4026292) | action | something an agent can do or perform | [Action (philosophy)](https://en.wikipedia.org/wiki/Action_%28philosophy%29) |
| [Q4057633](https://www.wikidata.org/wiki/Q4057633) | hierarchy of administrative territorial entities | structure by which a state is subdivided for administration |  |
| [Q4120621](https://www.wikidata.org/wiki/Q4120621) | rank | level in a hierarchy | [Rank](https://en.wikipedia.org/wiki/Rank) |
| [Q4164581](https://www.wikidata.org/wiki/Q4164581) | semigroupoid | partial algebra that satisfies the axioms for a small category | [Semigroupoid](https://en.wikipedia.org/wiki/Semigroupoid) |
| [Q4164871](https://www.wikidata.org/wiki/Q4164871) | position | social role with a set of powers and responsibilities within an organization |  |
| [Q4184950](https://www.wikidata.org/wiki/Q4184950) | regularity | abstract concept describing something that appears more than once with a certain space or time between the occurrences |  |
| [Q4263830](https://www.wikidata.org/wiki/Q4263830) | literary form | category of literary works distinguished by formal characteristics without consideration of content |  |
| [Q4303335](https://www.wikidata.org/wiki/Q4303335) | program | set of instructions used to control the behavior of a machine | [Program (machine)](https://en.wikipedia.org/wiki/Program_%28machine%29) |
| [Q4312352](https://www.wikidata.org/wiki/Q4312352) | lowest common ancestor | term in computer science | [Lowest common ancestor](https://en.wikipedia.org/wiki/Lowest_common_ancestor) |
| [Q4330518](https://www.wikidata.org/wiki/Q4330518) | object of study | something that undergoes testing or observation in a scientific experiment or in a scientific study |  |
| [Q4358176](https://www.wikidata.org/wiki/Q4358176) | council | group of people who come together to consult, deliberate, or make decisions | [Council](https://en.wikipedia.org/wiki/Council) |
| [Q4373292](https://www.wikidata.org/wiki/Q4373292) | physical property | attribute of a physical system or body; OR non-chemical property of a material | [Physical property](https://en.wikipedia.org/wiki/Physical_property) |
| [Q4391941](https://www.wikidata.org/wiki/Q4391941) | non-associative algebra | algebra over a field | [Non-associative algebra](https://en.wikipedia.org/wiki/Non-associative_algebra) |
| [Q4406616](https://www.wikidata.org/wiki/Q4406616) | concrete object | a particular or specific instance of an entity. To describe tangible or physical objects use Q223557 |  |
| [Q4455897](https://www.wikidata.org/wiki/Q4455897) | kinship term | a term to denote a familial connection |  |
| [Q4502142](https://www.wikidata.org/wiki/Q4502142) | visual artwork | work of art that is primarily visual |  |
| [Q4504549](https://www.wikidata.org/wiki/Q4504549) | religious role | occupation or position characterized by religious activity |  |
| [Q4671277](https://www.wikidata.org/wiki/Q4671277) | academic institution | educational institution dedicated to education and research | [Academic institution](https://en.wikipedia.org/wiki/Academic_institution) |
| [Q4671286](https://www.wikidata.org/wiki/Q4671286) | academic major | focus of academic study leading to a degree | [Academic major](https://en.wikipedia.org/wiki/Academic_major) |
| [Q4720939](https://www.wikidata.org/wiki/Q4720939) | closure | the smallest superset of a given set that is closed under a given operation | [Closure (mathematics)](https://en.wikipedia.org/wiki/Closure_%28mathematics%29) |
| [Q4830453](https://www.wikidata.org/wiki/Q4830453) | business | organization undertaking commercial, industrial, or professional activity | [Business](https://en.wikipedia.org/wiki/Business) |
| [Q4833865](https://www.wikidata.org/wiki/Q4833865) | abstract structure | type of abstraction in science, mathematics, and philosophy | [Abstract structure](https://en.wikipedia.org/wiki/Abstract_structure) |
| [Q4835091](https://www.wikidata.org/wiki/Q4835091) | territory | geographic region belonging to or controlled by a person or entity |  |
| [Q4887411](https://www.wikidata.org/wiki/Q4887411) | benefactor | person who gives some form of help to benefit a person, group or organization (the beneficiary) | [Benefactor (law)](https://en.wikipedia.org/wiki/Benefactor_%28law%29) |
| [Q4897819](https://www.wikidata.org/wiki/Q4897819) | role | identity of an item in relation to another specified item |  |
| [Q4903541](https://www.wikidata.org/wiki/Q4903541) | bicategory | structure consisting of a class of objects and (between every pair X,Y of objects) a category C(X,Y), along with composition functors C(X,Y)×C(Y,Z)→C(X,Z), such that composition is associative (up to natural equivalence by some isomorphism) | [Bicategory](https://en.wikipedia.org/wiki/Bicategory) |
| [Q5034491](https://www.wikidata.org/wiki/Q5034491) | capacity optimization | technologies used to improve storage use by shrinking stored data | [Capacity optimization](https://en.wikipedia.org/wiki/Capacity_optimization) |
| [Q5035794](https://www.wikidata.org/wiki/Q5035794) | capitalist state | concept of the state in a capitalist system | [Capitalist state](https://en.wikipedia.org/wiki/Capitalist_state) |
| [Q5127848](https://www.wikidata.org/wiki/Q5127848) | class | group of things derived from extensional or intensional definition (philosophy) | [Class (philosophy)](https://en.wikipedia.org/wiki/Class_%28philosophy%29) |
| [Q5135329](https://www.wikidata.org/wiki/Q5135329) | closed category | category with an internal hom functor | [Closed category](https://en.wikipedia.org/wiki/Closed_category) |
| [Q5135347](https://www.wikidata.org/wiki/Q5135347) | closed monoidal category | type of category in mathematics | [Closed monoidal category](https://en.wikipedia.org/wiki/Closed_monoidal_category) |
| [Q5140810](https://www.wikidata.org/wiki/Q5140810) | coequalizer | generalisation of quotient in category theory | [Coequalizer](https://en.wikipedia.org/wiki/Coequalizer) |
| [Q5155040](https://www.wikidata.org/wiki/Q5155040) | community project | any kind of project based on a community of people | [Community project](https://en.wikipedia.org/wiki/Community_project) |
| [Q5156940](https://www.wikidata.org/wiki/Q5156940) | oxygen compound | any chemical compound having at least one oxygen atom | [Oxygen compounds](https://en.wikipedia.org/wiki/Oxygen_compounds) |
| [Q5165061](https://www.wikidata.org/wiki/Q5165061) | content | extended-nonnegative-real-valued function defined on a field of sets (or more generally, a boolean algebra) that is additive over finitely many disjoint sets | [Content (measure theory)](https://en.wikipedia.org/wiki/Content_%28measure_theory%29) |
| [Q5244640](https://www.wikidata.org/wiki/Q5244640) | De Morgan algebra | system of logic lacking the excluded middle law | [De Morgan algebra](https://en.wikipedia.org/wiki/De_Morgan_algebra) |
| [Q5341295](https://www.wikidata.org/wiki/Q5341295) | educational organization | body with an aim of education |  |
| [Q5358404](https://www.wikidata.org/wiki/Q5358404) | electronic page | term to encompass paginated content in presentations or documents that originate or remain as visual electronic documents | [Electronic page](https://en.wikipedia.org/wiki/Electronic_page) |
| [Q5358816](https://www.wikidata.org/wiki/Q5358816) | element | concept in category theory | [Element (category theory)](https://en.wikipedia.org/wiki/Element_%28category_theory%29) |
| [Q5382940](https://www.wikidata.org/wiki/Q5382940) | epigroup | algebraic structure, a semigroup in which every element has a power that belongs to a subgroup | [Epigroup](https://en.wikipedia.org/wiki/Epigroup) |
| [Q5399590](https://www.wikidata.org/wiki/Q5399590) | essentially unique | mathematical terminology | [Essentially unique](https://en.wikipedia.org/wiki/Essentially_unique) |
| [Q5446431](https://www.wikidata.org/wiki/Q5446431) | fibered category | a “sheaf” of categories over a topological space (or, more generally, any category), where instead of equality we have natural equivalences in the definition of the sheaf axioms | [Fibred category](https://en.wikipedia.org/wiki/Fibred_category) |
| [Q5500272](https://www.wikidata.org/wiki/Q5500272) | free object | a “generic” algebraic structure over the given set, fulfilling no other equations except those given by the defining axioms | [Free object](https://en.wikipedia.org/wiki/Free_object) |
| [Q5500964](https://www.wikidata.org/wiki/Q5500964) | freely redistributable software | software that anyone is free to redistribute | [Freely redistributable software](https://en.wikipedia.org/wiki/Freely_redistributable_software) |
| [Q5513324](https://www.wikidata.org/wiki/Q5513324) | F₂ | finite field of order two | [GF(2)](https://en.wikipedia.org/wiki/GF%282%29) |
| [Q5555733](https://www.wikidata.org/wiki/Q5555733) | degree of kinship | degree of relationship between two people with a common ancester | [Degree of kinship](https://en.wikipedia.org/wiki/Degree_of_kinship) |
| [Q5569420](https://www.wikidata.org/wiki/Q5569420) | specialization (pre)order | preorder on the set of the points of a topological space | [Specialization preorder](https://en.wikipedia.org/wiki/Specialization_preorder) |
| [Q5589178](https://www.wikidata.org/wiki/Q5589178) | regime | form of government | [Regime](https://en.wikipedia.org/wiki/Regime) |
| [Q5891007](https://www.wikidata.org/wiki/Q5891007) | anatomically modern human | member of the species Homo sapiens with an appearance consistent with modern humans | [Anatomically modern human](https://en.wikipedia.org/wiki/Anatomically_modern_human) |
| [Q5891840](https://www.wikidata.org/wiki/Q5891840) | homotopy type theory | variant of type theory incorporating the univalence axiom of Voevodsky | [Homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) |
| [Q5962346](https://www.wikidata.org/wiki/Q5962346) | classification scheme | system of descriptive information for an arrangement or division of objects into groups based on characteristics, which the objects have in common | [Classification scheme (information science)](https://en.wikipedia.org/wiki/Classification_scheme_%28information_science%29) |
| [Q6005984](https://www.wikidata.org/wiki/Q6005984) | baryonic matter | matter consisting of baryons (bound states with odd numbers of quarks), electrons, and possibly other leptons, but not their antiparticles | [Baryonic matter](https://en.wikipedia.org/wiki/Baryonic_matter) |
| [Q6046311](https://www.wikidata.org/wiki/Q6046311) | interface standard | type of technical standard that describes one or more functional or physical characteristics to allow information exchange between devices | [Interface standard](https://en.wikipedia.org/wiki/Interface_standard) |
| [Q6047782](https://www.wikidata.org/wiki/Q6047782) | internal category | structure, with properties similar to a (small) category, constructed inside any category with pullbacks; two objects O (objects) and M (morphisms), equipped with arrows s, t: M → O (source/target), e: O → M (identity), m: M ₛ×ₜ M → M (composition) | [Internal category](https://en.wikipedia.org/wiki/Internal_category) |
| [Q6134913](https://www.wikidata.org/wiki/Q6134913) | Least fixed point | Smallest fixed point of a function from a poset | [Least fixed point](https://en.wikipedia.org/wiki/Least_fixed_point) |
| [Q6138701](https://www.wikidata.org/wiki/Q6138701) | RDF query language | programming language allowing easy querying on RDF graphs | [RDF query language](https://en.wikipedia.org/wiki/RDF_query_language) |
| [Q6423319](https://www.wikidata.org/wiki/Q6423319) | knowledge organization system | generic term used in knowledge organization about authority files, classification schemes, thesauri, topic maps, ontologies etc. | [Knowledge organization system](https://en.wikipedia.org/wiki/Knowledge_organization_system) |
| [Q6453739](https://www.wikidata.org/wiki/Q6453739) | primitive notion | undefined term motivated informally, usually by an appeal to intuition and everyday experience, or introduced axiomatically and eventually generated only by a series of elementary operations | [Primitive notion](https://en.wikipedia.org/wiki/Primitive_notion) |
| [Q6499736](https://www.wikidata.org/wiki/Q6499736) | vocabulary | body of words used in a particular language (or the set known to an individual) | [Vocabulary](https://en.wikipedia.org/wiki/Vocabulary) |
| [Q6501447](https://www.wikidata.org/wiki/Q6501447) | local government | lowest tier of administration within a sovereign state | [Local government](https://en.wikipedia.org/wiki/Local_government) |
| [Q6545185](https://www.wikidata.org/wiki/Q6545185) | unique identifier | identifier which is unique and permanent within a subset of space and time | [Unique identifier](https://en.wikipedia.org/wiki/Unique_identifier) |
| [Q6630149](https://www.wikidata.org/wiki/Q6630149) | narrative form | form of narration, either written or oral; aspect of literary classification |  |
| [Q6661985](https://www.wikidata.org/wiki/Q6661985) | data processing | any process that uses a computer program to enter data and summarise, analyse or otherwise convert data into usable information | [Data processing](https://en.wikipedia.org/wiki/Data_processing) |
| [Q6671777](https://www.wikidata.org/wiki/Q6671777) | structure | arrangement and organization of interrelated elements in an object or system, or the object or system so organized | [Structure](https://en.wikipedia.org/wiki/Structure) |
| [Q6918890](https://www.wikidata.org/wiki/Q6918890) | Moufang loop | algebraic structure | [Moufang loop](https://en.wikipedia.org/wiki/Moufang_loop) |
| [Q7048977](https://www.wikidata.org/wiki/Q7048977) | abstract entity | entity that does not have a physical existence, including abstract objects and properties | [Non-physical entity](https://en.wikipedia.org/wiki/Non-physical_entity) |
| [Q7049224](https://www.wikidata.org/wiki/Q7049224) | noncommutative ring | algebraic structure | [Noncommutative ring](https://en.wikipedia.org/wiki/Noncommutative_ring) |
| [Q7094076](https://www.wikidata.org/wiki/Q7094076) | online database | database accessible from a network, including from the Internet | [Online database](https://en.wikipedia.org/wiki/Online_database) |
| [Q7095059](https://www.wikidata.org/wiki/Q7095059) | ontology language | formal language used to construct ontologies | [Ontology language](https://en.wikipedia.org/wiki/Ontology_language) |
| [Q7098616](https://www.wikidata.org/wiki/Q7098616) | opposite category | category constructed from another category C, whose objects are the same as those of C, whose morphisms from X to Y are the same as the morphisms in C from Y to X | [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) |
| [Q7184903 → Q7048977](https://www.wikidata.org/wiki/Q7184903) | abstract entity | entity that does not have a physical existence, including abstract objects and properties | [Non-physical entity](https://en.wikipedia.org/wiki/Non-physical_entity) |
| [Q7189713](https://www.wikidata.org/wiki/Q7189713) | physiological condition | conditions of the external or internal milieu that may occur in nature for that organism | [Physiological condition](https://en.wikipedia.org/wiki/Physiological_condition) |
| [Q7210356](https://www.wikidata.org/wiki/Q7210356) | political organization | group involved with politics | [Political organisation](https://en.wikipedia.org/wiki/Political_organisation) |
| [Q7226641](https://www.wikidata.org/wiki/Q7226641) | polynomial identity ring |  | [Polynomial identity ring](https://en.wikipedia.org/wiki/Polynomial_identity_ring) |
| [Q7233031](https://www.wikidata.org/wiki/Q7233031) | thin category | category in which there are one or less morphism between every two objects | [Thin category](https://en.wikipedia.org/wiki/Thin_category) |
| [Q7241077](https://www.wikidata.org/wiki/Q7241077) | presheaf | contravariant functor to the category of sets and functions | [Presheaf (category theory)](https://en.wikipedia.org/wiki/Presheaf_%28category_theory%29) |
| [Q7249564](https://www.wikidata.org/wiki/Q7249564) | proleptic calendar | calendar that is applied to dates before its introduction | [Proleptic calendar](https://en.wikipedia.org/wiki/Proleptic_calendar) |
| [Q7269539](https://www.wikidata.org/wiki/Q7269539) | quasitransitive relation | type of binary relation | [Quasitransitive relation](https://en.wikipedia.org/wiki/Quasitransitive_relation) |
| [Q7271381](https://www.wikidata.org/wiki/Q7271381) | query | mapping from structures of one signature to structures of another vocabulary | [Query (complexity)](https://en.wikipedia.org/wiki/Query_%28complexity%29) |
| [Q7320446](https://www.wikidata.org/wiki/Q7320446) | rhetorical mode | variety, conventions, and purposes of language-based communication, particularly writing and speaking | [Modes of discourse](https://en.wikipedia.org/wiki/Modes_of_discourse) |
| [Q7406919](https://www.wikidata.org/wiki/Q7406919) | service | economic product that directly satisfies wants without producing a lasting asset | [Service (economics)](https://en.wikipedia.org/wiki/Service_%28economics%29) |
| [Q7449422](https://www.wikidata.org/wiki/Q7449422) | semigroup with involution | semigroup equipped with an involutive anti-automorphism | [Semigroup with involution](https://en.wikipedia.org/wiki/Semigroup_with_involution) |
| [Q7449424](https://www.wikidata.org/wiki/Q7449424) | Semigroup action | an action or act of a semigroup on a set | [Semigroup action](https://en.wikipedia.org/wiki/Semigroup_action) |
| [Q7551287](https://www.wikidata.org/wiki/Q7551287) | social object |  | [Social objects](https://en.wikipedia.org/wiki/Social_objects) |
| [Q7574764](https://www.wikidata.org/wiki/Q7574764) | Wormaldia quadriphylla | species of insect |  |
| [Q7595790](https://www.wikidata.org/wiki/Q7595790) | stably finite ring | property of rings (mathematics) | [Stably finite ring](https://en.wikipedia.org/wiki/Stably_finite_ring) |
| [Q7595945](https://www.wikidata.org/wiki/Q7595945) | stack | generalization (and categorification) of a sheaf; a fibered category that admits effective descent | [Stack (mathematics)](https://en.wikipedia.org/wiki/Stack_%28mathematics%29) |
| [Q7604698](https://www.wikidata.org/wiki/Q7604698) | statutory authority | body set up by law which is authorised to enact legislation | [Statutory body](https://en.wikipedia.org/wiki/Statutory_body) |
| [Q7631737](https://www.wikidata.org/wiki/Q7631737) | subobject classifier | in category theory | [Subobject classifier](https://en.wikipedia.org/wiki/Subobject_classifier) |
| [Q7662595](https://www.wikidata.org/wiki/Q7662595) | synonym | in a database, alternate name for a table, view, sequence, or other schema object in a database | [Synonym (database)](https://en.wikipedia.org/wiki/Synonym_%28database%29) |
| [Q7725310](https://www.wikidata.org/wiki/Q7725310) | series of creative works | ordered set of creative works | [Series fiction](https://en.wikipedia.org/wiki/Series_fiction) |
| [Q7725634](https://www.wikidata.org/wiki/Q7725634) | literary work | written work read for enjoyment or edification | [Literary work](https://en.wikipedia.org/wiki/Literary_work) |
| [Q7887142](https://www.wikidata.org/wiki/Q7887142) | unit of analysis | major entity that is being analyzed in a study | [Unit of analysis](https://en.wikipedia.org/wiki/Unit_of_analysis) |
| [Q7888828](https://www.wikidata.org/wiki/Q7888828) | Gaussian rational | complex number of the form p + qi, where p and q are both rational numbers | [Gaussian rational](https://en.wikipedia.org/wiki/Gaussian_rational) |
| [Q7930989](https://www.wikidata.org/wiki/Q7930989) | city or town | type of human settlement |  |
| [Q7977957](https://www.wikidata.org/wiki/Q7977957) | weak n-category | generalization of the strict notion of n-category | [Weak n-category](https://en.wikipedia.org/wiki/Weak_n-category) |
| [Q8027727](https://www.wikidata.org/wiki/Q8027727) | Wissenschaft | any area of scholarly study or science that involves systematic research and teaching, e.g., art history | [Wissenschaft](https://en.wikipedia.org/wiki/Wissenschaft) |
| [Q8187769](https://www.wikidata.org/wiki/Q8187769) | economic activity | human activity involving the transfer of goods or services |  |
| [Q8359428](https://www.wikidata.org/wiki/Q8359428) | social activist | activist focused on social issues | [Social activist](https://en.wikipedia.org/wiki/Social_activist) |
| [Q8424307](https://www.wikidata.org/wiki/Q8424307) | number with finite decimal representation | number that can be represented with a finite number of decimal places | [Finite decimal](https://en.wikipedia.org/wiki/Finite_decimal) |
| [Q8963063](https://www.wikidata.org/wiki/Q8963063) | discrete function |  | [Discrete function](https://en.wikipedia.org/wiki/Discrete_function) |
| [Q9337488](https://www.wikidata.org/wiki/Q9337488) | interval scale | measurement scale in which quantity values can be ranked and subtracted from each other | [Interval scale](https://en.wikipedia.org/wiki/Interval_scale) |
| [Q9388534](https://www.wikidata.org/wiki/Q9388534) | archival collection | collection of materials with some unifying characteristic, housed in an archive |  |
| [Q9392635](https://www.wikidata.org/wiki/Q9392635) | carbonyl compound | any chemical compound with a carbonyl group |  |
| [Q9584157](https://www.wikidata.org/wiki/Q9584157) | adult human | adult member of the human species |  |
| [Q10301427](https://www.wikidata.org/wiki/Q10301427) | moving image | series of visual representations imparting an impression of motion when shown in succession |  |
| [Q10372568](https://www.wikidata.org/wiki/Q10372568) | society | group of animals who live together with some form of organisation |  |
| [Q10383930](https://www.wikidata.org/wiki/Q10383930) | academic work | academic work that reports the result of study and analysis of a topic using scholarly methods |  |
| [Q10535634](https://www.wikidata.org/wiki/Q10535634) | initial object | category object with exactly one morphism leading from it to every object of the category |  |
| [Q10541491](https://www.wikidata.org/wiki/Q10541491) | legal form | type of legal entity within certain legal system |  |
| [Q10547012](https://www.wikidata.org/wiki/Q10547012) | common matter | matter, explicitly excluding any antimatter; physical substance containing neither non-matter nor antimatter |  |
| [Q10564851](https://www.wikidata.org/wiki/Q10564851) | closure operator | mathematical operator | [Closure operator](https://en.wikipedia.org/wiki/Closure_operator) |
| [Q10567583](https://www.wikidata.org/wiki/Q10567583) | small category | category whose objects and morphisms both form sets | [Small category](https://en.wikipedia.org/wiki/Small_category) |
| [Q10683158](https://www.wikidata.org/wiki/Q10683158) | substance | any composed matter whose origin is either biological, chemical, or mineral |  |
| [Q10711424](https://www.wikidata.org/wiki/Q10711424) | state with limited recognition | territory with de-facto sovereignty but lacking international acceptance | [State with limited recognition](https://en.wikipedia.org/wiki/State_with_limited_recognition) |
| [Q10843872](https://www.wikidata.org/wiki/Q10843872) | process | set of interrelated tasks that transform inputs into outputs, where the tasks may be carried out by people, nature or machines using various resources | [Process](https://en.wikipedia.org/wiki/Process) |
| [Q10864048](https://www.wikidata.org/wiki/Q10864048) | first-level administrative division | administrative division directly subordinate to or under administration of a national government | [First-level administrative division](https://en.wikipedia.org/wiki/First-level_administrative_division) |
| [Q11077412](https://www.wikidata.org/wiki/Q11077412) | strict order | irreflexive transitive relation | [Strict order](https://en.wikipedia.org/wiki/Strict_order) |
| [Q11235244](https://www.wikidata.org/wiki/Q11235244) | domain | connected open subset of a finite-dimensional vector space | [Domain (mathematical analysis)](https://en.wikipedia.org/wiki/Domain_%28mathematical_analysis%29) |
| [Q11268999](https://www.wikidata.org/wiki/Q11268999) | determination |  |  |
| [Q11418818](https://www.wikidata.org/wiki/Q11418818) | commercial capital city | not official title of a city where commerce is most active in a country |  |
| [Q11618417](https://www.wikidata.org/wiki/Q11618417) | LAU 2 | former designation type for local administrative units within the EU's NUTS geocode standard |  |
| [Q11666901](https://www.wikidata.org/wiki/Q11666901) | nominal kinship | all kin not directly related by blood |  |
| [Q11756524](https://www.wikidata.org/wiki/Q11756524) | p-adic integer |  | [P-adic integer](https://en.wikipedia.org/wiki/P-adic_integer) |
| [Q11826511](https://www.wikidata.org/wiki/Q11826511) | scientific work | distinct intellectual creation in science | [Scientific work](https://en.wikipedia.org/wiki/Scientific_work) |
| [Q11862829](https://www.wikidata.org/wiki/Q11862829) | academic discipline | academic field of study or profession | [Academic discipline](https://en.wikipedia.org/wiki/Academic_discipline) |
| [Q11953984](https://www.wikidata.org/wiki/Q11953984) | linguistic unit | any of a range of units of language, whether a word, phrase, clause, sentence, paragraph, whole conversation or a story, morpheme, grapheme, phoneme and syllable |  |
| [Q11997597](https://www.wikidata.org/wiki/Q11997597) | representative | occupation consisting in representing a physical or a moral person |  |
| [Q12042160](https://www.wikidata.org/wiki/Q12042160) | scientific non-fiction literature | literature on scientific topics | [Scientific literature](https://en.wikipedia.org/wiki/Scientific_literature) |
| [Q12046615](https://www.wikidata.org/wiki/Q12046615) | feature type | Wikidata metaclass for geographic feature |  |
| [Q12047512](https://www.wikidata.org/wiki/Q12047512) | psychological phenomenon | fact studied in psychology or a psychological event that manifests itself in a particular way | [Mental phenomena](https://en.wikipedia.org/wiki/Mental_phenomena) |
| [Q12047513](https://www.wikidata.org/wiki/Q12047513) | mental process | concept in psychology that refers to the sequence of thoughts, emotions, and behaviors that reflect the mind’s function and interaction with the environment | [Mental process](https://en.wikipedia.org/wiki/Mental_process) |
| [Q12050496](https://www.wikidata.org/wiki/Q12050496) | feature | any characteristic used to classify a phoneme or word | [Feature (linguistics)](https://en.wikipedia.org/wiki/Feature_%28linguistics%29) |
| [Q12132640](https://www.wikidata.org/wiki/Q12132640) | scientific terminology | part of the language that is used by scientists in the context of their professional activities | [Scientific terminology](https://en.wikipedia.org/wiki/Scientific_terminology) |
| [Q12139612](https://www.wikidata.org/wiki/Q12139612) | list | set of discrete items of information | [List](https://en.wikipedia.org/wiki/List) |
| [Q12175350](https://www.wikidata.org/wiki/Q12175350) | faithful functor | functor which is injective when restricted to every hom-set | [Faithful functor](https://en.wikipedia.org/wiki/Faithful_functor) |
| [Q12202238](https://www.wikidata.org/wiki/Q12202238) | transformation | function mapping a set to itself | [Transformation (function)](https://en.wikipedia.org/wiki/Transformation_%28function%29) |
| [Q12303449](https://www.wikidata.org/wiki/Q12303449) | caption | lines of text used to explain or elaborate an illustration, figure, table, or photograph | [Photo caption](https://en.wikipedia.org/wiki/Photo_caption) |
| [Q12338229](https://www.wikidata.org/wiki/Q12338229) | sperm donor | person who donates sperm | [Sperm donor](https://en.wikipedia.org/wiki/Sperm_donor) |
| [Q12379553](https://www.wikidata.org/wiki/Q12379553) | general term | term that denotes a more encompassing or ample concept with a generic relation | [Generic term](https://en.wikipedia.org/wiki/Generic_term) |
| [Q12488383](https://www.wikidata.org/wiki/Q12488383) | content | matter or entity that is contained |  |
| [Q12558574](https://www.wikidata.org/wiki/Q12558574) | point of view | standpoint regarding a topic; opinion, attitude, or judgment upon some matter; way that one looks at something | [Point of view (philosophy)](https://en.wikipedia.org/wiki/Point_of_view_%28philosophy%29) |
| [Q12569864](https://www.wikidata.org/wiki/Q12569864) | economic entity | one of the assumptions made in generally accepted accounting principles | [Economic entity](https://en.wikipedia.org/wiki/Economic_entity) |
| [Q12579633](https://www.wikidata.org/wiki/Q12579633) | invention | unique or novel device, method, composition or process; product of the process of invention | [Invention](https://en.wikipedia.org/wiki/Invention) |
| [Q12625119](https://www.wikidata.org/wiki/Q12625119) | blood kin | relative which one is related to biologically | [Blood relative](https://en.wikipedia.org/wiki/Blood_relative) |
| [Q12737077](https://www.wikidata.org/wiki/Q12737077) | occupation | label applied to a person based on an activity they participate in |  |
| [Q12758374](https://www.wikidata.org/wiki/Q12758374) | relative | person considered to have a family relationship with another |  |
| [Q12772052](https://www.wikidata.org/wiki/Q12772052) | multi-paradigm programming language | programming language type | [Multi-paradigm programming language](https://en.wikipedia.org/wiki/Multi-paradigm_programming_language) |
| [Q12774177](https://www.wikidata.org/wiki/Q12774177) | means | means by which a function is performed |  |
| [Q12775893](https://www.wikidata.org/wiki/Q12775893) | scheme | a basic outline drawn up in general and essential features |  |
| [Q12812139](https://www.wikidata.org/wiki/Q12812139) | specialized term | word or expression with a technical definition |  |
| [Q12819913](https://www.wikidata.org/wiki/Q12819913) | connection | process of joining or uniting entities to create a new entity |  |
| [Q13196193](https://www.wikidata.org/wiki/Q13196193) | part | separate element of a larger entity. For integral parts, see Q1310239. |  |
| [Q13218276](https://www.wikidata.org/wiki/Q13218276) | free city | city that governs itself |  |
| [Q13405586](https://www.wikidata.org/wiki/Q13405586) | non-fiction literature genre |  |  |
| [Q13406463](https://www.wikidata.org/wiki/Q13406463) | Wikimedia list article | page of a Wikimedia project with a list of something | [Wikipedia:Lists](https://en.wikipedia.org/wiki/Wikipedia%3ALists) |
| [Q13418847](https://www.wikidata.org/wiki/Q13418847) | historical event | particular incident in history that brings about a historical change |  |
| [Q13420330](https://www.wikidata.org/wiki/Q13420330) | provider | economic actor that provides goods or services to consumers |  |
| [Q13512116](https://www.wikidata.org/wiki/Q13512116) | nonassociative ring | generalization of a ring that does not require multiplication to be associative | [Nonassociative ring](https://en.wikipedia.org/wiki/Nonassociative_ring) |
| [Q13539802](https://www.wikidata.org/wiki/Q13539802) | place with town rights and privileges | place with town rights and privileges |  |
| [Q14204246](https://www.wikidata.org/wiki/Q14204246) | Wikimedia project page | page in the non-article namespace 4 on a Wikimedia project serving internal purposes |  |
| [Q14623681](https://www.wikidata.org/wiki/Q14623681) | Jane Belson | barrister, wife of science-fiction author Douglas Adams (1952–2011) |  |
| [Q14757767](https://www.wikidata.org/wiki/Q14757767) | fourth-level administrative division | administrative division subordinate to or under administration of a third-level division |  |
| [Q14827288](https://www.wikidata.org/wiki/Q14827288) | Wikimedia project | site or service hosted by the Wikimedia Foundation to serve the Wikimedia community | [Wikimedia project](https://en.wikipedia.org/wiki/Wikimedia_project) |
| [Q14946528](https://www.wikidata.org/wiki/Q14946528) | conflation | merging of distinct identities or concepts, usually erroneously | [Conflation](https://en.wikipedia.org/wiki/Conflation) |
| [Q15042037](https://www.wikidata.org/wiki/Q15042037) | statistical territorial entity | areas designated as significant due to high population density, economic activity, or other reasons |  |
| [Q15138389](https://www.wikidata.org/wiki/Q15138389) | Wikimedia article page | article in the main space of a Wikimedia site (note: various wikis, do NOT use this together with "instance of") |  |
| [Q15239622](https://www.wikidata.org/wiki/Q15239622) | disputed territory | territory, which status is controversial between two or more existing states | [Disputed territory](https://en.wikipedia.org/wiki/Disputed_territory) |
| [Q15474042](https://www.wikidata.org/wiki/Q15474042) | MediaWiki page | page on a MediaWiki wiki |  |
| [Q15534632](https://www.wikidata.org/wiki/Q15534632) | graded ring | graded module, where the grading has the structure of a monoid, in which ring multiplication respects the grading | [Graded ring](https://en.wikipedia.org/wiki/Graded_ring) |
| [Q15617994](https://www.wikidata.org/wiki/Q15617994) | administrative territorial entity type | type of administrative divisions, usually used in several countries |  |
| [Q15621286](https://www.wikidata.org/wiki/Q15621286) | intellectual work | work created through human thought and perception, including creative work |  |
| [Q15631850](https://www.wikidata.org/wiki/Q15631850) | districts and some cities of Germany | administrative units of Germany |  |
| [Q15633582](https://www.wikidata.org/wiki/Q15633582) | MediaWiki wiki | website editable by visitors whose software engine is MediaWiki |  |
| [Q15633587](https://www.wikidata.org/wiki/Q15633587) | MediaWiki main namespace page | page in the main namespace of a wiki, used for "main" content specific to the project such as article, lemma, ... |  |
| [Q15642541](https://www.wikidata.org/wiki/Q15642541) | human-geographic territorial entity | territorial entity of which the borders are determined by physiographic and human features |  |
| [Q15642566](https://www.wikidata.org/wiki/Q15642566) | non-political administrative territorial entity | country subdivision that does not have its own government and exists only for administrative purposes |  |
| [Q15709883](https://www.wikidata.org/wiki/Q15709883) | statistical definition | definition used by statistical organisms or studies |  |
| [Q15710813](https://www.wikidata.org/wiki/Q15710813) | physical structure | body or assemblage of bodies in space that form a system capable of supporting loads |  |
| [Q15712714](https://www.wikidata.org/wiki/Q15712714) | biomolecular structure | 3D conformation of a biological sequence, like DNA, RNA, proteins | [Biomolecular structure](https://en.wikipedia.org/wiki/Biomolecular_structure) |
| [Q15734684](https://www.wikidata.org/wiki/Q15734684) | Körperschaft des öffentlichen Rechts | form of corporate personhood in Germany |  |
| [Q15831325](https://www.wikidata.org/wiki/Q15831325) | class used in Universal Decimal Classification |  |  |
| [Q15835236](https://www.wikidata.org/wiki/Q15835236) | military action | use of the armed forces as a means of executive power |  |
| [Q15846555](https://www.wikidata.org/wiki/Q15846555) | completeness | fundamental concept in metalogic, and the term may be used without qualification with differing meanings depending on the context within mathematical logic | [Completeness (logic)](https://en.wikipedia.org/wiki/Completeness_%28logic%29) |
| [Q15851373](https://www.wikidata.org/wiki/Q15851373) | crosslink page | used to list articles associated with similar concepts |  |
| [Q15873243](https://www.wikidata.org/wiki/Q15873243) | Svorka | Wikimedia disambiguation page |  |
| [Q15893266](https://www.wikidata.org/wiki/Q15893266) | former entity | entity that no longer operates or is terminated |  |
| [Q15974307](https://www.wikidata.org/wiki/Q15974307) | Unitary municipality in Germany | administrative unit of Germany |  |
| [Q15975724](https://www.wikidata.org/wiki/Q15975724) | object of a category | constituent element of the mathematical notion of category | [Object of a category](https://en.wikipedia.org/wiki/Object_of_a_category) |
| [Q15978631](https://www.wikidata.org/wiki/Q15978631) | Homo sapiens | species of mammal | [Homo sapiens](https://en.wikipedia.org/wiki/Homo_sapiens) |
| [Q15980953](https://www.wikidata.org/wiki/Q15980953) | fiction series | sequence of works of fiction having certain characteristics in common |  |
| [Q16003513](https://www.wikidata.org/wiki/Q16003513) | NUTS (european administrative division classification) class |  |  |
| [Q16222597](https://www.wikidata.org/wiki/Q16222597) | Wikidata item | main documentary unit of Wikidata | [Wikidata item](https://en.wikipedia.org/wiki/Wikidata_item) |
| [Q16317911](https://www.wikidata.org/wiki/Q16317911) | positive integer | integer greater than zero; natural number explicitly excluding zero | [Positive integer](https://en.wikipedia.org/wiki/Positive_integer) |
| [Q16334295](https://www.wikidata.org/wiki/Q16334295) | group of humans | any set of human beings | [Humans](https://en.wikipedia.org/wiki/Humans) |
| [Q16334298](https://www.wikidata.org/wiki/Q16334298) | group of living things | set of live individual entities of any nature |  |
| [Q16547118](https://www.wikidata.org/wiki/Q16547118) | surrogate mother | woman who agrees to become pregnant and deliver a child for another party |  |
| [Q16562419](https://www.wikidata.org/wiki/Q16562419) | political entity | territorial political body such as a state or local government |  |
| [Q16686022](https://www.wikidata.org/wiki/Q16686022) | natural physical object | natural thing that exists that humans did not make |  |
| [Q16686448](https://www.wikidata.org/wiki/Q16686448) | artificial object | anything created through intelligent or artificial means (either material or mental) |  |
| [Q16887380](https://www.wikidata.org/wiki/Q16887380) | group | well-defined, enumerable collection of discrete entities that form a collective whole |  |
| [Q16889133](https://www.wikidata.org/wiki/Q16889133) | class | collection of items defined by common characteristics | [Class (knowledge representation)](https://en.wikipedia.org/wiki/Class_%28knowledge_representation%29) |
| [Q16911578](https://www.wikidata.org/wiki/Q16911578) | ∞-groupoid | abstract homotopical model for topological spaces | [∞-groupoid](https://en.wikipedia.org/wiki/%E2%88%9E-groupoid) |
| [Q16944486](https://www.wikidata.org/wiki/Q16944486) | elaboration | adding more information to existing information for clarity | [Elaboration](https://en.wikipedia.org/wiki/Elaboration) |
| [Q17006903](https://www.wikidata.org/wiki/Q17006903) | decomposable measure | measure that is a disjoint union of finite measures | [Decomposable measure](https://en.wikipedia.org/wiki/Decomposable_measure) |
| [Q17020770](https://www.wikidata.org/wiki/Q17020770) | Boolean-valued function | function with two-element codomain | [Boolean-valued function](https://en.wikipedia.org/wiki/Boolean-valued_function) |
| [Q17077830](https://www.wikidata.org/wiki/Q17077830) | groupoid object | generalization of a groupoid and a group objects | [Groupoid object](https://en.wikipedia.org/wiki/Groupoid_object) |
| [Q17091170](https://www.wikidata.org/wiki/Q17091170) | group conflict | hostilities between different groups | [Group conflict](https://en.wikipedia.org/wiki/Group_conflict) |
| [Q17102802](https://www.wikidata.org/wiki/Q17102802) | rng | algebraic structure similar to ring but not necessarily having a multiplicative identity | [Rng (algebra)](https://en.wikipedia.org/wiki/Rng_%28algebra%29) |
| [Q17103860](https://www.wikidata.org/wiki/Q17103860) | symmetric monoidal category | monoidal category where A ⊗ B is naturally equivalent to B ⊗ A | [Symmetric monoidal category](https://en.wikipedia.org/wiki/Symmetric_monoidal_category) |
| [Q17104046](https://www.wikidata.org/wiki/Q17104046) | mixed graph | graph that is permitted to contain both directed and undirected edges | [Mixed graph](https://en.wikipedia.org/wiki/Mixed_graph) |
| [Q17138290](https://www.wikidata.org/wiki/Q17138290) | kinship system | ides about familiar relationships |  |
| [Q17141489](https://www.wikidata.org/wiki/Q17141489) | intersection | concept in mathematics | [Intersection](https://en.wikipedia.org/wiki/Intersection) |
| [Q17152639](https://www.wikidata.org/wiki/Q17152639) | thesaurus | controlled vocabulary expanded with relations of broader, narrower and related terms, serving subject indexing and vocabulary control | [Thesaurus (information retrieval)](https://en.wikipedia.org/wiki/Thesaurus_%28information_retrieval%29) |
| [Q17176533](https://www.wikidata.org/wiki/Q17176533) | software component | software package, web service, web resource, or module that encapsulates a set of related functions | [Software component](https://en.wikipedia.org/wiki/Software_component) |
| [Q17197366](https://www.wikidata.org/wiki/Q17197366) | type of organization | type in a typology; form of social organization defined by the structure of the relationship between its members, or between other organizations |  |
| [Q17320256](https://www.wikidata.org/wiki/Q17320256) | physical process | any sequence of events or changes that occur in the physical world, governed by the laws of physics, involving energy, matter, or their interactions |  |
| [Q17334923](https://www.wikidata.org/wiki/Q17334923) | physical location | position of something in space |  |
| [Q17339814](https://www.wikidata.org/wiki/Q17339814) | group or class of chemical substances | set of chemical substances that share a common characteristic |  |
| [Q17362920](https://www.wikidata.org/wiki/Q17362920) | Wikimedia duplicated page | this item duplicates another item, it can be merged once the necessary merges are done in other Wikimedia projects |  |
| [Q17379835](https://www.wikidata.org/wiki/Q17379835) | Wikimedia page outside the main knowledge tree | instance of this class should only describe a Wikimedia page, not the outside world concept described in the page |  |
| [Q17442446](https://www.wikidata.org/wiki/Q17442446) | Wikimedia internal item | instances and/or subclasses of this item are about some Wikimedia-only content and should not refer to real world entities |  |
| [Q17489659](https://www.wikidata.org/wiki/Q17489659) | group of works | any set of works |  |
| [Q17524420](https://www.wikidata.org/wiki/Q17524420) | aspect of history | topic viewed from a historical point of view |  |
| [Q17537576](https://www.wikidata.org/wiki/Q17537576) | creative work | artistic creation | [Creative work](https://en.wikipedia.org/wiki/Creative_work) |
| [Q17538690](https://www.wikidata.org/wiki/Q17538690) | group of manifestations | set of manifestations as defined in FRBR |  |
| [Q17587456](https://www.wikidata.org/wiki/Q17587456) | sitelink | RDF node |  |
| [Q17625380](https://www.wikidata.org/wiki/Q17625380) | hierarchical classification | classification system based on hierarchical rules | [Hierarchical classification](https://en.wikipedia.org/wiki/Hierarchical_classification) |
| [Q17710986](https://www.wikidata.org/wiki/Q17710986) | literary pentalogy | set of five books |  |
| [Q18199114](https://www.wikidata.org/wiki/Q18199114) | algebraic construction | method by which an algebraic entity is defined or derived from another |  |
| [Q18205845](https://www.wikidata.org/wiki/Q18205845) | cartesian monoidal category | monoidal category with respect to products | [Cartesian monoidal category](https://en.wikipedia.org/wiki/Cartesian_monoidal_category) |
| [Q18206693](https://www.wikidata.org/wiki/Q18206693) | E-dense semigroup | semigroup in which every element a has at least one weak inverse x, | [E-dense semigroup](https://en.wikipedia.org/wiki/E-dense_semigroup) |
| [Q18247357](https://www.wikidata.org/wiki/Q18247357) | group of structures or buildings | architectural structures or buildings that do not form a building complex, but are treated as a group |  |
| [Q18340964](https://www.wikidata.org/wiki/Q18340964) | power | philosophical concept | [Power (philosophy)](https://en.wikipedia.org/wiki/Power_%28philosophy%29) |
| [Q18386809](https://www.wikidata.org/wiki/Q18386809) | partial algebra | generalization of universal algebra to partial operations | [Partial algebra](https://en.wikipedia.org/wiki/Partial_algebra) |
| [Q18386814](https://www.wikidata.org/wiki/Q18386814) | partial groupoid | algebraic structure | [Partial groupoid](https://en.wikipedia.org/wiki/Partial_groupoid) |
| [Q18603648](https://www.wikidata.org/wiki/Q18603648) | contributing factor | circumstance or event that contributes to a result, but is not 100% determinative of outcome |  |
| [Q18616576](https://www.wikidata.org/wiki/Q18616576) | Wikidata property | part of statements according to the Wikidata data model, appearing as the 2nd item in the statement triple | [Wikidata property](https://en.wikipedia.org/wiki/Wikidata_property) |
| [Q18647515](https://www.wikidata.org/wiki/Q18647515) | transitive Wikidata property | to be used to declare properties to be transitive; OWL language construct |  |
| [Q18647518](https://www.wikidata.org/wiki/Q18647518) | symmetric property | used to declare properties to be symmetric; equivalent to owl:SymmetricProperty |  |
| [Q18786106](https://www.wikidata.org/wiki/Q18786106) | topology | (structure) collection of open subsets of a topological space | [Topology (structure)](https://en.wikipedia.org/wiki/Topology_%28structure%29) |
| [Q19474404](https://www.wikidata.org/wiki/Q19474404) | single-value constraint | type of constraint for Wikidata properties: used to specify that this property generally contains a single value per item |  |
| [Q19478619](https://www.wikidata.org/wiki/Q19478619) | metaclass | class which has instances that are all themselves classes | [Metaclass (knowledge representation)](https://en.wikipedia.org/wiki/Metaclass_%28knowledge_representation%29) |
| [Q19798642](https://www.wikidata.org/wiki/Q19798642) | Wikibase value | part of a claim in Wikibase data model |  |
| [Q19798644](https://www.wikidata.org/wiki/Q19798644) | Wikibase data model element | abstract object |  |
| [Q19798645](https://www.wikidata.org/wiki/Q19798645) | Wikibase datatype | defines for Wikibase how correspondingly labelled data values are to be processed and displayed |  |
| [Q19798647](https://www.wikidata.org/wiki/Q19798647) | concept of no-value in Wikibase | value attributed to a claim when we are sure that the property has no value for an element, in Wikibase wikis |  |
| [Q19798648](https://www.wikidata.org/wiki/Q19798648) | concept of unknown value in Wikibase | Wikibase data model concept, (*do not use in statements*) value given to a claim when we know there is a value for the property but don't know the value |  |
| [Q19798651](https://www.wikidata.org/wiki/Q19798651) | wikibase data model possible value for a claim | in Wikibase Data Model, no-value, some-value or the values defined by datatypes |  |
| [Q19798657](https://www.wikidata.org/wiki/Q19798657) | Wikibase value type | every value in Wikibase can be either no-value or unknown or an actual value |  |
| [Q19822352](https://www.wikidata.org/wiki/Q19822352) | stepparent | parent's spouse who is not one's biological parent | [Stepparent](https://en.wikipedia.org/wiki/Stepparent) |
| [Q19832712](https://www.wikidata.org/wiki/Q19832712) | historical administrative division | administrative division which existed in the past, that may or may not still exist (Use subclass Q19953632 for divisions which no longer exist) |  |
| [Q19833078](https://www.wikidata.org/wiki/Q19833078) | surjective relation | binary relation such that every element of the right set has a corresponding element in the left set | [Surjective relation](https://en.wikipedia.org/wiki/Surjective_relation) |
| [Q19847637](https://www.wikidata.org/wiki/Q19847637) | Wikidata property for an identifier | Wikidata property to identify something in an external source |  |
| [Q19868531](https://www.wikidata.org/wiki/Q19868531) | formal ontology concept | formally defined concept in the context of an ontology |  |
| [Q19885597](https://www.wikidata.org/wiki/Q19885597) | oxo compound | class of chemical compounds that contain a doubly bonded oxygen atom |  |
| [Q19902884](https://www.wikidata.org/wiki/Q19902884) | Wikidata property definition |  |  |
| [Q19953632](https://www.wikidata.org/wiki/Q19953632) | former administrative territorial entity | administrative division which is no longer in use |  |
| [Q19967801](https://www.wikidata.org/wiki/Q19967801) | online service | product or service provided on the Internet | [Online service](https://en.wikipedia.org/wiki/Online_service) |
| [Q20026918](https://www.wikidata.org/wiki/Q20026918) | mathematical theory | mathematical model that is based on axioms | [Mathematical theory](https://en.wikipedia.org/wiki/Mathematical_theory) |
| [Q20642780](https://www.wikidata.org/wiki/Q20642780) | mathematical construction |  |  |
| [Q20665666](https://www.wikidata.org/wiki/Q20665666) | conclusion | the proposition arrived at by logical reasoning |  |
| [Q20667921](https://www.wikidata.org/wiki/Q20667921) | type of French administrative division |  |  |
| [Q20746742](https://www.wikidata.org/wiki/Q20746742) | adoptive parent | person who has become the child's parent through the legal process of adoption |  |
| [Q20819677](https://www.wikidata.org/wiki/Q20819677) | technical specification | list of technical characteristics describing an object or process |  |
| [Q20826540](https://www.wikidata.org/wiki/Q20826540) | scholar | someone who has great knowledge | [Scholar](https://en.wikipedia.org/wiki/Scholar) |
| [Q20829075](https://www.wikidata.org/wiki/Q20829075) | type of language | Wikidata metaclass of langoid in linguistic typology |  |
| [Q20920559](https://www.wikidata.org/wiki/Q20920559) | procedure | standardised method of carrying out a task |  |
| [Q20936777](https://www.wikidata.org/wiki/Q20936777) | series of specified number of works | ordered set of a given number of creative works |  |
| [Q21004260](https://www.wikidata.org/wiki/Q21004260) | inquiry | process that has the aim of augmenting knowledge, resolving doubt, or solving a problem | [Inquiry](https://en.wikipedia.org/wiki/Inquiry) |
| [Q21006424](https://www.wikidata.org/wiki/Q21006424) | legal obligation | legal requirement to take some course of action |  |
| [Q21040055](https://www.wikidata.org/wiki/Q21040055) | aspect | perspective from which a certain subject may be discussed |  |
| [Q21044622](https://www.wikidata.org/wiki/Q21044622) | Wikidata statement rank | attribute of a statement on Wikidata | [Wikidata rank](https://en.wikipedia.org/wiki/Wikidata_rank) |
| [Q21146257](https://www.wikidata.org/wiki/Q21146257) | type | kind or variety of something |  |
| [Q21157127](https://www.wikidata.org/wiki/Q21157127) | cluster | collection of entities that are physically or conceptually close to each other |  |
| [Q21170479](https://www.wikidata.org/wiki/Q21170479) | possibility | quality of being possible; the condition or fact of being possible |  |
| [Q21281405](https://www.wikidata.org/wiki/Q21281405) | Wikidata internal entity | instances of this entity are about some Wikidata-only content and should not refer to real world entities |  |
| [Q21406562](https://www.wikidata.org/wiki/Q21406562) | field | term which refers to either a (commutative) field or a division ring |  |
| [Q21481766](https://www.wikidata.org/wiki/Q21481766) | scholarly chapter | chapter written by specific authors in a scholarly book |  |
| [Q21502402](https://www.wikidata.org/wiki/Q21502402) | property constraint | constraint of a Wikidata property |  |
| [Q21502410](https://www.wikidata.org/wiki/Q21502410) | distinct-values constraint | type of constraint for Wikidata properties: used to specify that the value for this property is likely to be different from all other items |  |
| [Q21502838](https://www.wikidata.org/wiki/Q21502838) | conflicts-with constraint | type of constraint for Wikidata properties: used to specify that an item must not have a given statement |  |
| [Q21503247](https://www.wikidata.org/wiki/Q21503247) | item-requires-statement constraint | type of constraint for Wikidata properties: used to specify that an item with this property should also have another given property |  |
| [Q21503250](https://www.wikidata.org/wiki/Q21503250) | subject type constraint | type of constraint for Wikidata properties: used to specify that the item described by such properties should be a subclass or instance of a given type |  |
| [Q21510855](https://www.wikidata.org/wiki/Q21510855) | inverse constraint | type of constraint for Wikidata properties: used to specify that the referenced item has to refer back to this item with the given inverse property |  |
| [Q21510859](https://www.wikidata.org/wiki/Q21510859) | one-of constraint | type of constraint for Wikidata properties: used to specify that the value for this property has to be one of a given set of items |  |
| [Q21510863](https://www.wikidata.org/wiki/Q21510863) | used as qualifier constraint | type of constraint for Wikidata properties: used to specify that a property must only be used as a qualifier |  |
| [Q21510864](https://www.wikidata.org/wiki/Q21510864) | value-requires-statement constraint | type of constraint for Wikidata properties: used to specify that the referenced item should have a statement with a given property |  |
| [Q21510865](https://www.wikidata.org/wiki/Q21510865) | value-type constraint | type of constraint for Wikidata properties: used to specify that the value item should be a subclass or instance of a given type |  |
| [Q21550639](https://www.wikidata.org/wiki/Q21550639) | geometric concept | mathematical concepts, scientific concepts |  |
| [Q21562092](https://www.wikidata.org/wiki/Q21562092) | imperative programming language | programming language implementing the imperative programming paradigm |  |
| [Q21855572](https://www.wikidata.org/wiki/Q21855572) | additive object | additively-composing abstract object |  |
| [Q21871294](https://www.wikidata.org/wiki/Q21871294) | group or class of living things | second-order class of living things |  |
| [Q22269697](https://www.wikidata.org/wiki/Q22269697) | multi-organism process | biological process which involves another organism of the same or different species |  |
| [Q22294683](https://www.wikidata.org/wiki/Q22294683) | biological process involved in intraspecies interaction between organisms | process in which an organism has an effect on an organism of the same species |  |
| [Q22299433](https://www.wikidata.org/wiki/Q22299433) | multicellular organismal process | any biological process, occurring at the level of a multicellular organism, pertinent to its function |  |
| [Q22675015](https://www.wikidata.org/wiki/Q22675015) | type of quantum particle | type or family of quantum mechanical particles, often subatomic but also may be unrelated to atoms |  |
| [Q22689055](https://www.wikidata.org/wiki/Q22689055) | Fawaz bin Saud bin Abdul Aziz Al Saud |  |  |
| [Q22811234](https://www.wikidata.org/wiki/Q22811234) | branch of philosophy | subdivision of the field of philosophy | [Branch of philosophy](https://en.wikipedia.org/wiki/Branch_of_philosophy) |
| [Q22923920](https://www.wikidata.org/wiki/Q22923920) | territorial collectivity of France with special status |  |  |
| [Q22963169](https://www.wikidata.org/wiki/Q22963169) | additive map | Z-module homomorphism | [Additive map](https://en.wikipedia.org/wiki/Additive_map) |
| [Q23808682](https://www.wikidata.org/wiki/Q23808682) | conservative functor | functor that reflects isomorphisms | [Conservative functor](https://en.wikipedia.org/wiki/Conservative_functor) |
| [Q23894381](https://www.wikidata.org/wiki/Q23894381) | actor | participant in an event that instigates it |  |
| [Q23958852](https://www.wikidata.org/wiki/Q23958852) | variable-order class | abstract entity representing classes whose instances may be classes of different orders or even non-classes |  |
| [Q23958946](https://www.wikidata.org/wiki/Q23958946) | individual entity | entity, be it a thing, a person or any other agent, which is identifiable by its determined characteristics, as contrasted to a class whose characteristics may be varying among its instances |  |
| [Q23959932](https://www.wikidata.org/wiki/Q23959932) | fixed-order class | class whose instances are all either individuals or same-fixed-order classes | [Fixed-order class](https://en.wikipedia.org/wiki/Fixed-order_class) |
| [Q24017414](https://www.wikidata.org/wiki/Q24017414) | second-order class | metaclass containing as instances all classes of individuals | [Second-order class](https://en.wikipedia.org/wiki/Second-order_class) |
| [Q24017465](https://www.wikidata.org/wiki/Q24017465) | third-order class | metaclass containing as instances all classes of classes of individuals |  |
| [Q24027474](https://www.wikidata.org/wiki/Q24027474) | fourth-order class | metaclass containing as instances all classes of classes of classes of individuals |  |
| [Q24027515](https://www.wikidata.org/wiki/Q24027515) | fifth-order class | metaclass containing as instances all fifth-order classes |  |
| [Q24027526](https://www.wikidata.org/wiki/Q24027526) | fixed-order class of higher order | class of order strictly higher than 5 |  |
| [Q24034552](https://www.wikidata.org/wiki/Q24034552) | mathematical concept | abstract entity in mathematics | [Mathematical concept](https://en.wikipedia.org/wiki/Mathematical_concept) |
| [Q24229398](https://www.wikidata.org/wiki/Q24229398) | being | distinct and identifiable entity with agency, capable of performing actions |  |
| [Q24238356](https://www.wikidata.org/wiki/Q24238356) | unknown | entity whose identity is not known |  |
| [Q24249534](https://www.wikidata.org/wiki/Q24249534) | specialised classification scheme | classification system focused on a specific subject area |  |
| [Q24902509](https://www.wikidata.org/wiki/Q24902509) | human activity | activity initiated by a human, intentionally or unintentionally |  |
| [Q25098571](https://www.wikidata.org/wiki/Q25098571) | first-degree relative | one's offspring, sibling or parent | [First-degree relative](https://en.wikipedia.org/wiki/First-degree_relative) |
| [Q25601835](https://www.wikidata.org/wiki/Q25601835) | close relative | relation with few degrees of separation |  |
| [Q26256810](https://www.wikidata.org/wiki/Q26256810) | topic | topic or area addressed by a work or set of works |  |
| [Q26884324](https://www.wikidata.org/wiki/Q26884324) | Wikimedia outline article | hierarchical list showing relationships between topics and their subtopics | [Wikipedia:Outlines](https://en.wikipedia.org/wiki/Wikipedia%3AOutlines) |
| [Q26897143](https://www.wikidata.org/wiki/Q26897143) | set system | (non-indexed) set whose all elements are subsets of another common set |  |
| [Q26907166](https://www.wikidata.org/wiki/Q26907166) | temporal entity | thing that can be contained within a period of time, or change in state (e.g. events, periods, acts) |  |
| [Q27043950](https://www.wikidata.org/wiki/Q27043950) | anatomical entity | biological entity that is either member of a species or a unit of its structural organization |  |
| [Q27096213](https://www.wikidata.org/wiki/Q27096213) | geographic entity | relatively stationary place or entity that can be geographically identified, located, or described |  |
| [Q27096235](https://www.wikidata.org/wiki/Q27096235) | artificial geographic entity | non-natural geographic entities such as settlements, infrastructure, and excavations |  |
| [Q27702623](https://www.wikidata.org/wiki/Q27702623) | academic enclave |  |  |
| [Q27949697](https://www.wikidata.org/wiki/Q27949697) | Wikibase reason for deprecated rank | used with "reason for deprecated rank" (P2241) |  |
| [Q28017710](https://www.wikidata.org/wiki/Q28017710) | digital platform | online infrastructure where users can exchange information | [Digital platform (infrastructure)](https://en.wikipedia.org/wiki/Digital_platform_%28infrastructure%29) |
| [Q28062188](https://www.wikidata.org/wiki/Q28062188) | book set | collection of book editions having certain characteristics in common that informally allow their identification together as a group |  |
| [Q28314507](https://www.wikidata.org/wiki/Q28314507) | recurring entity | temporal entity that recurs |  |
| [Q28458059](https://www.wikidata.org/wiki/Q28458059) | graded-commutative ring | (ℤ/2)-graded ring in which even elements commute among themselves, odd elements anticommute among themselves, and even and odd elements commute | [Graded-commutative ring](https://en.wikipedia.org/wiki/Graded-commutative_ring) |
| [Q28555911](https://www.wikidata.org/wiki/Q28555911) | ordinary matter | matter composed of protons, neutrons, and/or electrons |  |
| [Q28693603](https://www.wikidata.org/wiki/Q28693603) | quantum particle | quantum mechanical particle in nuclear, atomic, and particle physics; often subatomic; composed of elementary particle(s) |  |
| [Q28732711](https://www.wikidata.org/wiki/Q28732711) | physical substance | substance composed of quantum particle(s)/field(s), such as matter and/or radiation; that of which objects/systems are composed; physical stuff that can be considered concrete (not strictly abstract) |  |
| [Q28813620](https://www.wikidata.org/wiki/Q28813620) | set | group of items regarded as one |  |
| [Q28859120](https://www.wikidata.org/wiki/Q28859120) | cardinal measurement scale | measurement scale whose level of measurement is numeric and not merely a ranking (ordinal) or naming (nominal) |  |
| [Q28864853](https://www.wikidata.org/wiki/Q28864853) | patronage | pledging to support a child or children |  |
| [Q28872924](https://www.wikidata.org/wiki/Q28872924) | designation for an administrative territorial entity of a single country | type of administrative divisions, used in one country |  |
| [Q28877390](https://www.wikidata.org/wiki/Q28877390) | massive quantum particle | quantum-mechanical particle (elementary or composite) having real positive rest mass |  |
| [Q28923017](https://www.wikidata.org/wiki/Q28923017) | strict programming language | programming language | [Strict programming language](https://en.wikipedia.org/wiki/Strict_programming_language) |
| [Q28923954](https://www.wikidata.org/wiki/Q28923954) | languoid class | e.g. dialect, language, macrolanguage, language subfamily, family, or superfamily; each instance of these is a subclass of languoid |  |
| [Q29018101](https://www.wikidata.org/wiki/Q29018101) | upper semilattice | partially ordered set that has a least upper bound for any nonempty finite subset |  |
| [Q29018102](https://www.wikidata.org/wiki/Q29018102) | lower semilattice | partially ordered set that has a greatest lower bound for any nonempty finite subset |  |
| [Q29028649](https://www.wikidata.org/wiki/Q29028649) | economic concept | concept used in economic sciences |  |
| [Q29377880](https://www.wikidata.org/wiki/Q29377880) | Shape Expressions | language for validating, describing or transforming RDF graphs | [ShEx](https://en.wikipedia.org/wiki/ShEx) |
| [Q29428373](https://www.wikidata.org/wiki/Q29428373) | tetrad | concrete group of 4 specific members |  |
| [Q29428403](https://www.wikidata.org/wiki/Q29428403) | pentad | concrete group of 5 specific members |  |
| [Q29431432](https://www.wikidata.org/wiki/Q29431432) | dyad | concrete group of 2 specific members |  |
| [Q29479670](https://www.wikidata.org/wiki/Q29479670) | undesirable characteristic | characteristic |  |
| [Q29888377](https://www.wikidata.org/wiki/Q29888377) | nominal locution | combination of words that acts as a noun |  |
| [Q29934200](https://www.wikidata.org/wiki/Q29934200) | Wikibase item | entity type for Wikibase items |  |
| [Q29934218](https://www.wikidata.org/wiki/Q29934218) | Wikibase property | entity type in Wikibase |  |
| [Q30060700](https://www.wikidata.org/wiki/Q30060700) | scientific object | type of object |  |
| [Q30241068](https://www.wikidata.org/wiki/Q30241068) | observable entity | entity which can be experienced or observed directly by human senses |  |
| [Q30503704](https://www.wikidata.org/wiki/Q30503704) | graph algorithm | type of algorithm | [Graph algorithm](https://en.wikipedia.org/wiki/Graph_algorithm) |
| [Q30588174](https://www.wikidata.org/wiki/Q30588174) | prestack | fibered category satisfying full and faithful (but not necessarily effective) descent | [Prestack](https://en.wikipedia.org/wiki/Prestack) |
| [Q30590669](https://www.wikidata.org/wiki/Q30590669) | quasitopos | finitely complete, finitely cocomplete, locally cartesian closed category with a classifier of strong monomorphisms | [Quasitopos](https://en.wikipedia.org/wiki/Quasitopos) |
| [Q31381203](https://www.wikidata.org/wiki/Q31381203) | RDF literal | A specific value, such as a string or a number, that is assigned to a resource. |  |
| [Q31384986](https://www.wikidata.org/wiki/Q31384986) | language-tagged string RDF literal | RDF literal |  |
| [Q31464082](https://www.wikidata.org/wiki/Q31464082) | source entity | entity (person, place, text, thing, etc.) from which something (information, goods, etc.) comes or is acquired |  |
| [Q31479975](https://www.wikidata.org/wiki/Q31479975) | communication system | type of system |  |
| [Q32753077](https://www.wikidata.org/wiki/Q32753077) | Wikidata entity | Wikidata data model element | [Wikidata entity](https://en.wikipedia.org/wiki/Wikidata_entity) |
| [Q33002955](https://www.wikidata.org/wiki/Q33002955) | knowledge graph | information repository structured as a graph of entities and relationships | [Knowledge graph](https://en.wikipedia.org/wiki/Knowledge_graph) |
| [Q33059348](https://www.wikidata.org/wiki/Q33059348) | full functor | Functor surjective on Hom sets | [Full functor](https://en.wikipedia.org/wiki/Full_functor) |
| [Q33104069](https://www.wikidata.org/wiki/Q33104069) | political concept | idea, theory, or notion primarily discussed in a political science and/or politics context |  |
| [Q33104129](https://www.wikidata.org/wiki/Q33104129) | sociological concept | abstract entity in sociology |  |
| [Q33104279](https://www.wikidata.org/wiki/Q33104279) | philosophical concept | concept used in philosophy |  |
| [Q33104303](https://www.wikidata.org/wiki/Q33104303) | concept in physics | concept relating to physics |  |
| [Q33120867](https://www.wikidata.org/wiki/Q33120867) | Wikimedia wiki | MediaWiki project run by the Wikimedia Foundation |  |
| [Q33120876](https://www.wikidata.org/wiki/Q33120876) | Wikimedia content project | wiki hosted by the Wikimedia Foundation that provides free knowledge | [Wikimedia content project](https://en.wikipedia.org/wiki/Wikimedia_content_project) |
| [Q35825432](https://www.wikidata.org/wiki/Q35825432) | converter | entity that converts, modifies, or transforms, producing an change of state, observable on the entity itself or on other objects |  |
| [Q36509592](https://www.wikidata.org/wiki/Q36509592) | wiki with script conversion | wikis that support language conversion syntaxes |  |
| [Q36808958](https://www.wikidata.org/wiki/Q36808958) | element of set | item that is a part of a set |  |
| [Q36993249](https://www.wikidata.org/wiki/Q36993249) | arranging | act of arranging items in some orderly way |  |
| [Q37787110](https://www.wikidata.org/wiki/Q37787110) | file system object | object in a computer filesystem, such as a file, directory, or symlink |  |
| [Q37866906](https://www.wikidata.org/wiki/Q37866906) | information resource | resource meant to distribute information |  |
| [Q38885242](https://www.wikidata.org/wiki/Q38885242) | physico-chemical property | type of property |  |
| [Q39725049](https://www.wikidata.org/wiki/Q39725049) | type of publication | Wikidata metaclass for the characteristics of a publication, e. g. the way in which a work is published |  |
| [Q39875001](https://www.wikidata.org/wiki/Q39875001) | measure | standard against which something can be judged |  |
| [Q41205988](https://www.wikidata.org/wiki/Q41205988) | 8-tuple | tuple of specific length (tuple length n=8) |  |
| [Q41773366](https://www.wikidata.org/wiki/Q41773366) | NUTS 3 statistical territorial entity |  |  |
| [Q41883552](https://www.wikidata.org/wiki/Q41883552) | combinatorial algorithm | type of algorithm |  |
| [Q42744322](https://www.wikidata.org/wiki/Q42744322) | urban municipality in Germany | municipality with town privileges in Germany (may e.g. legally prepend "Stadt" to its name) |  |
| [Q42866132](https://www.wikidata.org/wiki/Q42866132) | upper bound | any element M of a partially ordered set A which includes a subset B, such that M is greater than or equal to every element of B |  |
| [Q43460564](https://www.wikidata.org/wiki/Q43460564) | chemical entity | physical entity including chemical substances and other molecular entities |  |
| [Q43649390](https://www.wikidata.org/wiki/Q43649390) | Wikidata Q identifier | unique identifier (UID) used in Wikidata | [Wikidata identifier](https://en.wikipedia.org/wiki/Wikidata_identifier) |
| [Q43667189](https://www.wikidata.org/wiki/Q43667189) | donor | relationship with a charity |  |
| [Q44106280](https://www.wikidata.org/wiki/Q44106280) | idempotent function | function f such that its composition with itself equals f |  |
| [Q44292661](https://www.wikidata.org/wiki/Q44292661) | Wikidata reference | citation used to support a Wikidata statement | [Wikidata reference](https://en.wikipedia.org/wiki/Wikidata_reference) |
| [Q44292881](https://www.wikidata.org/wiki/Q44292881) | Wikidata statement | any statement or property value listed on Wikidata | [Wikidata statement](https://en.wikipedia.org/wiki/Wikidata_statement) |
| [Q45025858](https://www.wikidata.org/wiki/Q45025858) | depicting object | object providing a depiction |  |
| [Q47008575](https://www.wikidata.org/wiki/Q47008575) | s-finite measure | measure that is a countable sum of finite measures | [S-finite measure](https://en.wikipedia.org/wiki/S-finite_measure) |
| [Q47154513](https://www.wikidata.org/wiki/Q47154513) | structural class of chemical entities | set of chemical entities sharing a common structural feature to which is attached a variable part (or parts) defining a specific entity of the class |  |
| [Q47279819](https://www.wikidata.org/wiki/Q47279819) | type of mathematical function | type or family of mathematical function |  |
| [Q47460393](https://www.wikidata.org/wiki/Q47460393) | type of number | metaclass of classes containing numbers |  |
| [Q47461344](https://www.wikidata.org/wiki/Q47461344) | written work | any work expressed in writing, such as inscriptions, manuscripts, documents or maps |  |
| [Q47496130](https://www.wikidata.org/wiki/Q47496130) | reduction | decrease in a quantity |  |
| [Q48907157](https://www.wikidata.org/wiki/Q48907157) | section of populated place | inhabited territory part of a human settlement |  |
| [Q48937186](https://www.wikidata.org/wiki/Q48937186) | word or phrase | sequence of one or more words |  |
| [Q48998319](https://www.wikidata.org/wiki/Q48998319) | Frobenius reciprocity | duality between the process of restricting and inducting in representation theory | [Frobenius reciprocity](https://en.wikipedia.org/wiki/Frobenius_reciprocity) |
| [Q50081413](https://www.wikidata.org/wiki/Q50081413) | Wikipedia article page | article in the main space of a Wikipedia site (note: only wikipedia, do NOT use this together with "instance of") | [Wikipedia article](https://en.wikipedia.org/wiki/Wikipedia_article) |
| [Q50843083](https://www.wikidata.org/wiki/Q50843083) | off-side rule language | class of programming or markup languages that adhere to the off-side rule |  |
| [Q51885771](https://www.wikidata.org/wiki/Q51885771) | Wikibase lexeme | Wikibase entity type for lexemes |  |
| [Q51929311](https://www.wikidata.org/wiki/Q51929311) | largest city | city which has the greatest population in a country |  |
| [Q52551684](https://www.wikidata.org/wiki/Q52551684) | historical geographic location | countries known in remote history (as Byzantium) or former names of countries reflecting political changes in the 19th or 20th century (as East Germany) |  |
| [Q52558054](https://www.wikidata.org/wiki/Q52558054) | none-of constraint | constraint specifying values that should not be used for the given property |  |
| [Q53617407](https://www.wikidata.org/wiki/Q53617407) | material entity | independent continuant that is spatially extended whose identity is independent of that of other entities and can be maintained through time |  |
| [Q53617489](https://www.wikidata.org/wiki/Q53617489) | independent continuant | BFO subclass of persistant entities, which separately includes material entities and immaterial entities |  |
| [Q54285143](https://www.wikidata.org/wiki/Q54285143) | Wikibase form | Wikibase property value datatype |  |
| [Q54285715](https://www.wikidata.org/wiki/Q54285715) | Wikibase sense | Wikibase entity type for lexicographic senses |  |
| [Q54933429](https://www.wikidata.org/wiki/Q54933429) | left-unique relation | binary relation such that every element of the left set has at most one corresponding element in the right set | [Injective relation](https://en.wikipedia.org/wiki/Injective_relation) |
| [Q54938846](https://www.wikidata.org/wiki/Q54938846) | endorelation | binary relation whose domain and codomain coincide | [Homogeneous relation](https://en.wikipedia.org/wiki/Homogeneous_relation) |
| [Q54980267](https://www.wikidata.org/wiki/Q54980267) | intransitivity | property of binary endorelations | [Intransitivity](https://en.wikipedia.org/wiki/Intransitivity) |
| [Q55568967](https://www.wikidata.org/wiki/Q55568967) | biological structure | matter organized by living organisms |  |
| [Q55597235](https://www.wikidata.org/wiki/Q55597235) | class of living thing | different stages, states, and types of an organism |  |
| [Q55915575](https://www.wikidata.org/wiki/Q55915575) | scholarly work | work that reports the result of study and analysis of a topic using scholarly methods, including non-academic works |  |
| [Q55983715](https://www.wikidata.org/wiki/Q55983715) | organisms known by a particular common name | organisms which have been assigned common names in addition to their taxon name |  |
| [Q56055944](https://www.wikidata.org/wiki/Q56055944) | type of arts | form of the arts distinguished by its medium of expression (e.g. literature, music, visual arts) |  |
| [Q56256178](https://www.wikidata.org/wiki/Q56256178) | class of chemical entities with similar source or occurrence | set of chemical entities sharing a similar source or occurence |  |
| [Q56273712](https://www.wikidata.org/wiki/Q56273712) | source-available software | software distributed with its source code | [Source-available software](https://en.wikipedia.org/wiki/Source-available_software) |
| [Q56427813](https://www.wikidata.org/wiki/Q56427813) | type of legal entity in France | legal entity used in the France |  |
| [Q56512863](https://www.wikidata.org/wiki/Q56512863) | participant | person or object that takes part in an event or process |  |
| [Q56575300](https://www.wikidata.org/wiki/Q56575300) | ecological concept | concept in ecology |  |
| [Q56648173](https://www.wikidata.org/wiki/Q56648173) | archives | whole of the documents made and received by a juridical or physical person or organization in the conduct of affairs, and preserved |  |
| [Q58494026](https://www.wikidata.org/wiki/Q58494026) | Wikimedia page | page on a Wikimedia project |  |
| [Q59138870](https://www.wikidata.org/wiki/Q59138870) | digital object | in information science, a digital representation (i.e. computer file, such as a JPG) of a described object or record, which may be associated with its descriptive metadata |  |
| [Q59157859](https://www.wikidata.org/wiki/Q59157859) | secondary information |  |  |
| [Q59211454](https://www.wikidata.org/wiki/Q59211454) | level of description | in archival science, the position of the descriptive unit in the hierarchy of records |  |
| [Q60461402](https://www.wikidata.org/wiki/Q60461402) | HTML document | a HyperText Markup Language file |  |
| [Q60551191](https://www.wikidata.org/wiki/Q60551191) | Graph Query Language | graph query programming language under development by the ISO/IEC Joint Technical Committee 1 | [Graph Query Language](https://en.wikipedia.org/wiki/Graph_Query_Language) |
| [Q60790315](https://www.wikidata.org/wiki/Q60790315) | automorphism group | mathematical group formed from the automorphisms of an object | [Automorphism group](https://en.wikipedia.org/wiki/Automorphism_group) |
| [Q60971579](https://www.wikidata.org/wiki/Q60971579) | destructive behavior | type of behavior that leads to needs not getting met and loneliness long-term |  |
| [Q61961344](https://www.wikidata.org/wiki/Q61961344) | group of physical objects |  |  |
| [Q62210692](https://www.wikidata.org/wiki/Q62210692) | OWL ontology | ontology expressed in the Web Ontology Language (OWL) |  |
| [Q63872616](https://www.wikidata.org/wiki/Q63872616) | layout component | graphic component of visual presentation of text and images such as a page or poster |  |
| [Q63981612](https://www.wikidata.org/wiki/Q63981612) | product category | group of related products |  |
| [Q64513524](https://www.wikidata.org/wiki/Q64513524) | economic term | technical term; word or phrase that is part of economics terminology |  |
| [Q64588497](https://www.wikidata.org/wiki/Q64588497) | accounting term | technical term; word or phrase that is part of accounting terminology, generally accepted accounting principles |  |
| [Q64732777](https://www.wikidata.org/wiki/Q64732777) | biological phenomenon | biological process, property or characteristic of an organism, across the biosphere |  |
| [Q66310127](https://www.wikidata.org/wiki/Q66310127) | immaterial component | abstract entity forming a self-contained part of a larger entity |  |
| [Q66363468](https://www.wikidata.org/wiki/Q66363468) | non-biological parent | parent that is not the biologial progenitor of their child |  |
| [Q66363648](https://www.wikidata.org/wiki/Q66363648) | biological mother | female parent who contributed biologically to a child | [Biological mother](https://en.wikipedia.org/wiki/Biological_mother) |
| [Q66363655](https://www.wikidata.org/wiki/Q66363655) | legal parent | legal term in relation to kinship |  |
| [Q66363751](https://www.wikidata.org/wiki/Q66363751) | adoptive family | legal non-biological family |  |
| [Q66363776](https://www.wikidata.org/wiki/Q66363776) | family structure | type of social structure |  |
| [Q66371304](https://www.wikidata.org/wiki/Q66371304) | genetic parent |  |  |
| [Q66371306](https://www.wikidata.org/wiki/Q66371306) | genetic mother | woman who gave DNA to the child |  |
| [Q66394244](https://www.wikidata.org/wiki/Q66394244) | physical anatomical entity | physical entity with an anatomical form (structural, capable of dissection) |  |
| [Q66560214](https://www.wikidata.org/wiki/Q66560214) | biological macromolecule |  |  |
| [Q66661745](https://www.wikidata.org/wiki/Q66661745) | group of artificial physical objects | group of physical objects made or shaped by human hand |  |
| [Q66664364](https://www.wikidata.org/wiki/Q66664364) | linguistic term | type of technical term; word or phrase that is part of linguistics terminology |  |
| [Q66666685](https://www.wikidata.org/wiki/Q66666685) | academic professional | professional with an academic degree |  |
| [Q66707394](https://www.wikidata.org/wiki/Q66707394) | countable set | set with the same cardinality as some subset of the set of natural numbers | [Countable set](https://en.wikipedia.org/wiki/Countable_set) |
| [Q66747126](https://www.wikidata.org/wiki/Q66747126) | computer science term | technical term; word or phrase that is part of computer science terminology |  |
| [Q66747521](https://www.wikidata.org/wiki/Q66747521) | geography term | technical term; word or phrase that is part of geography terminology |  |
| [Q66785817](https://www.wikidata.org/wiki/Q66785817) | mathematical terminology | language used in the field of mathematics |  |
| [Q66786238](https://www.wikidata.org/wiki/Q66786238) | mathematical term | technical term: word or expression that is part of mathematical terminology |  |
| [Q67123843](https://www.wikidata.org/wiki/Q67123843) | town divided by border | town that is divided by border |  |
| [Q67518978](https://www.wikidata.org/wiki/Q67518978) | occurrent | entity that unfolds itself in time, or instantaneous boundary of such an entity (for example a beginning or an ending), or temporal or spatiotemporal region that such an entity occupies |  |
| [Q68023621](https://www.wikidata.org/wiki/Q68023621) | element of a field | element in an underlying set of a field |  |
| [Q68200780](https://www.wikidata.org/wiki/Q68200780) | scholarly literature | formal publications on matters of scholarship |  |
| [Q68482296](https://www.wikidata.org/wiki/Q68482296) | military activity | human activity by or related to military forces |  |
| [Q69886747](https://www.wikidata.org/wiki/Q69886747) | child rearing | training or bringing-up of children by parents or parent-substitutes |  |
| [Q71266556](https://www.wikidata.org/wiki/Q71266556) | warfare and armed conflicts | war or military conflict against another nation or organized group |  |
| [Q71533031](https://www.wikidata.org/wiki/Q71533031) | preferred rank | type of Wikibase rank indicating greater reliability or validity |  |
| [Q71533077](https://www.wikidata.org/wiki/Q71533077) | Wikibase reason for preferred rank | used with "reason for preferred rank" (P7452) |  |
| [Q71550118](https://www.wikidata.org/wiki/Q71550118) | individual quantity | superclass of physical, chemical, ... quantity; members are individual quantities like 5 kg, 2 apples, ... |  |
| [Q71574018](https://www.wikidata.org/wiki/Q71574018) | organooxygen compound | any organic compound containing at least one carbon-oxygen bond |  |
| [Q71758646](https://www.wikidata.org/wiki/Q71758646) | general quantity | first-order metaclass of quantities; instances include the classes physical quantity, chemical quantity, base quantity, intensive quantity, ... |  |
| [Q71782942](https://www.wikidata.org/wiki/Q71782942) | pnictogen compound | class of chemical compounds containing any of N, P, As, Sb, Bi |  |
| [Q72070508](https://www.wikidata.org/wiki/Q72070508) | group or class of chemical entities | set of chemical entities that shares a common characteristic |  |
| [Q73737153](https://www.wikidata.org/wiki/Q73737153) | normal rank | type of Wikibase rank |  |
| [Q73737357](https://www.wikidata.org/wiki/Q73737357) | deprecated rank | used to tag incorrect values |  |
| [Q74892521](https://www.wikidata.org/wiki/Q74892521) | imprecise class of chemical entities | set of chemical entities with imprecisely defined common features, that have no classification value |  |
| [Q76272846](https://www.wikidata.org/wiki/Q76272846) | oxygen molecular entity |  |  |
| [Q77730568](https://www.wikidata.org/wiki/Q77730568) | graph theory term | technical term; word or phrase that is part of graph theory terminology |  |
| [Q78054942](https://www.wikidata.org/wiki/Q78054942) | preordered set | set equipped with a preorder |  |
| [Q78081419](https://www.wikidata.org/wiki/Q78081419) | multivariate function | function with more than one argument |  |
| [Q86098365](https://www.wikidata.org/wiki/Q86098365) | currently empty class | class which currently contains no elements, but elements may have existed in the past and may exist in the future |  |
| [Q86923152](https://www.wikidata.org/wiki/Q86923152) | risk source | fundamental driver, circumstance or action that causes risks in a project, organization, or any other entity |  |
| [Q87075524](https://www.wikidata.org/wiki/Q87075524) | health risk | potentially adverse or negative health consequence due to a specific event, disease, condition, or hazard |  |
| [Q88392887](https://www.wikidata.org/wiki/Q88392887) | part of a work | part that a work consists of (use a more specific object if possible) |  |
| [Q91305654](https://www.wikidata.org/wiki/Q91305654) | discontinuous function | function which exhibits at least one discontinuity | [Discontinuous function](https://en.wikipedia.org/wiki/Discontinuous_function) |
| [Q91432273](https://www.wikidata.org/wiki/Q91432273) | terminal object | category object with exactly one morphism leading to it from every object of the category |  |
| [Q91773244](https://www.wikidata.org/wiki/Q91773244) | homotopy class | equivalence class of continuous maps up to homotopy | [Homotopy class](https://en.wikipedia.org/wiki/Homotopy_class) |
| [Q93447297](https://www.wikidata.org/wiki/Q93447297) | reflexive transitive closure | operation on binary relations | [Reflexive transitive closure](https://en.wikipedia.org/wiki/Reflexive_transitive_closure) |
| [Q93468132](https://www.wikidata.org/wiki/Q93468132) | hexadecad | A concrete group of 16 specific members |  |
| [Q93868746](https://www.wikidata.org/wiki/Q93868746) | numeric identifier | identifier whose values must be numbers (in any base) |  |
| [Q94250127](https://www.wikidata.org/wiki/Q94250127) | oriented graph | directed graph having no bidirected edges | [Oriented graph](https://en.wikipedia.org/wiki/Oriented_graph) |
| [Q94945104](https://www.wikidata.org/wiki/Q94945104) | anatomical metaclass |  |  |
| [Q95744479](https://www.wikidata.org/wiki/Q95744479) | additive function | function that preserves sums |  |
| [Q96088545](https://www.wikidata.org/wiki/Q96088545) | former geographical object | geographical object that has been abandoned, destroyed or demolished |  |
| [Q96116695](https://www.wikidata.org/wiki/Q96116695) | type of system | Wikidata metaclass of sets of interacting or interdependent components |  |
| [Q96196009](https://www.wikidata.org/wiki/Q96196009) | former or current state | political state, whether former or current |  |
| [Q96247293](https://www.wikidata.org/wiki/Q96247293) | type of management | Wikidata metaclass for management or administration, in terms of application area or category |  |
| [Q96251598](https://www.wikidata.org/wiki/Q96251598) | type of object | Wikidata metaclass of object, which could be concrete or abstract |  |
| [Q96253971](https://www.wikidata.org/wiki/Q96253971) | type of property | Wikidata metaclass of property or attribute |  |
| [Q96634632](https://www.wikidata.org/wiki/Q96634632) | psychology concept | concept used in the science of the psyche |  |
| [Q97152390](https://www.wikidata.org/wiki/Q97152390) | partial semigroup | algebraic structure |  |
| [Q97152408](https://www.wikidata.org/wiki/Q97152408) | partial binary operation | partially defined mathematical operation that combines two elements to produce another element |  |
| [Q97302511](https://www.wikidata.org/wiki/Q97302511) | partial operation | partially defined mathematical procedure which produces a result from operands; calculation from zero or more input values (called operands) to an output value |  |
| [Q97396140](https://www.wikidata.org/wiki/Q97396140) | partial group action on a set | generalization of a group action |  |
| [Q97669203](https://www.wikidata.org/wiki/Q97669203) | macromolecular conformation | large-scale 3D shape of a macromolecule (or supramolecular assembly of macromolecules) |  |
| [Q98099755](https://www.wikidata.org/wiki/Q98099755) | flexible magma | algebraic structure in which (a*b)*a = a*(b*a) | [Flexible magma](https://en.wikipedia.org/wiki/Flexible_magma) |
| [Q98119401](https://www.wikidata.org/wiki/Q98119401) | group or class of physical objects | category of physical objects that share the same characteristics |  |
| [Q98929991](https://www.wikidata.org/wiki/Q98929991) | place | small area known by a geographical name | [Paraje](https://en.wikipedia.org/wiki/Paraje) |
| [Q98966309](https://www.wikidata.org/wiki/Q98966309) | classification of human settlements | type of classification system |  |
| [Q99018632](https://www.wikidata.org/wiki/Q99018632) | group of geographic locations | set of several geographic entities spread over a geographic region |  |
| [Q99469810](https://www.wikidata.org/wiki/Q99469810) | type of fixed-size set or group | type of collection of entities that is defined by the number of elements or parts |  |
| [Q99527517](https://www.wikidata.org/wiki/Q99527517) | collective entity | entity that is a composite of other entities |  |
| [Q99541706](https://www.wikidata.org/wiki/Q99541706) | historical unrecognized state | nonexistent state that lacked recognition during its period of existence |  |
| [Q100195948](https://www.wikidata.org/wiki/Q100195948) | relative quality | quality that an item only possesses in relation to another item, or quality of multiple items in relation to each other |  |
| [Q100320664](https://www.wikidata.org/wiki/Q100320664) | concept in linguistics | theoretical concept used in the formal study of language |  |
| [Q100724091](https://www.wikidata.org/wiki/Q100724091) | physics term | technical term: word or expression that is part of physics terminology |  |
| [Q101208084](https://www.wikidata.org/wiki/Q101208084) | type of risk | Wikidata metaclass for risk or hazard |  |
| [Q103812671](https://www.wikidata.org/wiki/Q103812671) | anatomical entity type | metaclass for biological entities that are either member of a species or a unit of its structural organization |  |
| [Q103940464](https://www.wikidata.org/wiki/Q103940464) | continuant | entity that persists, endures, or continues to exist through time while maintaining its identity |  |
| [Q103994247](https://www.wikidata.org/wiki/Q103994247) | medical metaclass |  |  |
| [Q103995117](https://www.wikidata.org/wiki/Q103995117) | medical entity type | top-level metaclass for entities related to medicine |  |
| [Q103997018](https://www.wikidata.org/wiki/Q103997018) | direct anatomical metaclass | anatomical metaclass that has direct instances |  |
| [Q103997133](https://www.wikidata.org/wiki/Q103997133) | indirect anatomical metaclass | anatomical metaclass that has no direct instances |  |
| [Q104007623](https://www.wikidata.org/wiki/Q104007623) | anatomical entity class type |  |  |
| [Q104054982](https://www.wikidata.org/wiki/Q104054982) | ontological root | entity of an controlled vocabulary where all other entities of the ontology subclass it |  |
| [Q104086571](https://www.wikidata.org/wiki/Q104086571) | first-order class | class whose instances are individuals and not classes | [First-order class](https://en.wikipedia.org/wiki/First-order_class) |
| [Q104098715](https://www.wikidata.org/wiki/Q104098715) | territorial entity type |  |  |
| [Q104127086](https://www.wikidata.org/wiki/Q104127086) | memory | information stored in the mind, including facts, knowledge, skills, and episodic memories |  |
| [Q104637332](https://www.wikidata.org/wiki/Q104637332) | planned process | process that takes place with human or agentic involvement or planning |  |
| [Q104637420](https://www.wikidata.org/wiki/Q104637420) | sourcing circumstance | base class for P1480 qualifier values |  |
| [Q105606485](https://www.wikidata.org/wiki/Q105606485) | intellectual activity | human activity comprising of mental actions |  |
| [Q105770631](https://www.wikidata.org/wiki/Q105770631) | English Wikipedia article | unit of English Wikipedia |  |
| [Q105948247](https://www.wikidata.org/wiki/Q105948247) | knowledge system | systems of knowledge produced over time through interactions with other human beings |  |
| [Q106110777](https://www.wikidata.org/wiki/Q106110777) | predecessor | entity which is followed by another one in a sequence or order |  |
| [Q106213450](https://www.wikidata.org/wiki/Q106213450) | time-based visual work | visual artwork that depend on technology, and have duration as a dimension |  |
| [Q106411346](https://www.wikidata.org/wiki/Q106411346) | characterization | thorough description using analytical methods |  |
| [Q106559804](https://www.wikidata.org/wiki/Q106559804) | person or organization | class of agents |  |
| [Q106573263](https://www.wikidata.org/wiki/Q106573263) | ambiguous label | label that may refer to one of several specific items, and whose referent must be determined by context |  |
| [Q106668099](https://www.wikidata.org/wiki/Q106668099) | corporate body | in library science, a collective agent that is composed of persons who are organized for a common purpose or activity; collective agent includes corporate bodies and families |  |
| [Q107223533](https://www.wikidata.org/wiki/Q107223533) | relation (mathematics) |  | [Relation (mathematics)](https://en.wikipedia.org/wiki/Relation_%28mathematics%29) |
| [Q107307154](https://www.wikidata.org/wiki/Q107307154) | virtual place | any digitally created environment |  |
| [Q107344349](https://www.wikidata.org/wiki/Q107344349) | organic oxygen compound | any organic compound having at least one oxygen atom in the structure |  |
| [Q107649491](https://www.wikidata.org/wiki/Q107649491) | type of Wikidata property | Wikidata metaclass for properties |  |
| [Q107659597](https://www.wikidata.org/wiki/Q107659597) | Wikidata label |  | [Wikidata label](https://en.wikipedia.org/wiki/Wikidata_label) |
| [Q107659723](https://www.wikidata.org/wiki/Q107659723) | Wikidata alias |  | [Wikidata alias](https://en.wikipedia.org/wiki/Wikidata_alias) |
| [Q107659784](https://www.wikidata.org/wiki/Q107659784) | Wikidata description | Wikidata paramater containing information about its item | [Wikidata description](https://en.wikipedia.org/wiki/Wikidata_description) |
| [Q108060110](https://www.wikidata.org/wiki/Q108060110) | Wikidata term | type of string associated with entities in Wikidata, covers labels, descriptions and aliases |  |
| [Q108178728](https://www.wikidata.org/wiki/Q108178728) | national capital | capital of a sovereign state |  |
| [Q108329096](https://www.wikidata.org/wiki/Q108329096) | art genre by arts form | refers to a genre which is exactly the intersection between an art form and a more general art genre |  |
| [Q108466143](https://www.wikidata.org/wiki/Q108466143) | non-fiction genre | metaclass for genres related to narrative works of any form, that intends, in good faith, to present only truth and accuracy regarding information, events, or people |  |
| [Q108586636](https://www.wikidata.org/wiki/Q108586636) | form of event | metaclass, grouping forms and types of events by specificity |  |
| [Q108637623](https://www.wikidata.org/wiki/Q108637623) | integrating resource | a resource added to or changed over time by means of updates incorporated into the whole without remaining discrete |  |
| [Q109243379](https://www.wikidata.org/wiki/Q109243379) | modification | activity that creates, alters or otherwise changes an object in some particular characteristic without changing it into something else |  |
| [Q109542218](https://www.wikidata.org/wiki/Q109542218) | class of parts | the instances of this class are classes whose instances are parts of something |  |
| [Q109551565](https://www.wikidata.org/wiki/Q109551565) | sub-set of literature | refers to a set of written work having some characteristics in common |  |
| [Q109956737](https://www.wikidata.org/wiki/Q109956737) | union of several sets |  |  |
| [Q109957042](https://www.wikidata.org/wiki/Q109957042) | intersection of several sets |  |  |
| [Q110227435](https://www.wikidata.org/wiki/Q110227435) | past occurrence | occurrence that has already taken place |  |
| [Q110314665](https://www.wikidata.org/wiki/Q110314665) | type of error | Wikidata metaclass of error or fault |  |
| [Q110402867](https://www.wikidata.org/wiki/Q110402867) | knowledge classification | Wikidata metaclass |  |
| [Q110403031](https://www.wikidata.org/wiki/Q110403031) | knowledge type | Wikidata metaclass |  |
| [Q110720714](https://www.wikidata.org/wiki/Q110720714) | Identity type | concept in mathematics | [Identity type](https://en.wikipedia.org/wiki/Identity_type) |
| [Q110765110](https://www.wikidata.org/wiki/Q110765110) | first-order formula | well-formed formula belonging to a first-order language | [First-order formula](https://en.wikipedia.org/wiki/First-order_formula) |
| [Q110765126](https://www.wikidata.org/wiki/Q110765126) | first-order query | query using first-order logic as query language | [First-order query](https://en.wikipedia.org/wiki/First-order_query) |
| [Q110832782](https://www.wikidata.org/wiki/Q110832782) | software resource | part of a software application accessible, whether it be a data or a program |  |
| [Q110832792](https://www.wikidata.org/wiki/Q110832792) | database object | defined object in a database that is used to store or reference data. For example, a table or a sequence | [Database object](https://en.wikipedia.org/wiki/Database_object) |
| [Q110854677](https://www.wikidata.org/wiki/Q110854677) | network resource | software resource accesible by a network |  |
| [Q110879282](https://www.wikidata.org/wiki/Q110879282) | video and/or audio work | work containing video and/or audio |  |
| [Q110910970](https://www.wikidata.org/wiki/Q110910970) | visual work | work that conveys information through visual perception |  |
| [Q111204834](https://www.wikidata.org/wiki/Q111204834) | colimit | category theory concept that generalizes disjoint unions of sets, direct sums of modules, etc. | [Colimit](https://en.wikipedia.org/wiki/Colimit) |
| [Q111279923](https://www.wikidata.org/wiki/Q111279923) | wiki page | page on a wiki |  |
| [Q111360549](https://www.wikidata.org/wiki/Q111360549) | type of physical object | broad classification of material objects |  |
| [Q111485852](https://www.wikidata.org/wiki/Q111485852) | unital magma | algebraic structure | [Unital magma](https://en.wikipedia.org/wiki/Unital_magma) |
| [Q111513007](https://www.wikidata.org/wiki/Q111513007) | Wikibase entity | entity in Wikibase |  |
| [Q111513337](https://www.wikidata.org/wiki/Q111513337) | Wikibase entity ID | identifier for a Wikibase entity |  |
| [Q111513370](https://www.wikidata.org/wiki/Q111513370) | Wikidata entity ID | identifier for an entity on Wikidata |  |
| [Q111513406](https://www.wikidata.org/wiki/Q111513406) | Wikibase statement | statement in Wikibase |  |
| [Q111513414](https://www.wikidata.org/wiki/Q111513414) | Wikibase referenceRecord | reference in Wikibase |  |
| [Q111513443](https://www.wikidata.org/wiki/Q111513443) | Wikibase statement rank |  |  |
| [Q111667622](https://www.wikidata.org/wiki/Q111667622) | trigintaduonion | 32-dimensional hypercomplex number | [Trigintaduonion](https://en.wikipedia.org/wiki/Trigintaduonion) |
| [Q111752858](https://www.wikidata.org/wiki/Q111752858) | physicochemical process | process of physical and/or chemical change in a material or object |  |
| [Q111796904](https://www.wikidata.org/wiki/Q111796904) | type of equilibrium | Wikidata metaclass of abstraction underlying equilibrium or balance |  |
| [Q111931734](https://www.wikidata.org/wiki/Q111931734) | effect | exercising influence over an entity |  |
| [Q111972893](https://www.wikidata.org/wiki/Q111972893) | type of structure | Wikidata metaclass of arrangement and organization of interrelated elements in an object or system |  |
| [Q112057532](https://www.wikidata.org/wiki/Q112057532) | type of technology | Wikidata metaclass, used as "instance of" for every "subclass of" technology |  |
| [Q112160790](https://www.wikidata.org/wiki/Q112160790) | Dedekind-finite ring | ring in which left inverses are always right inverses | [Dedekind-finite ring](https://en.wikipedia.org/wiki/Dedekind-finite_ring) |
| [Q112234259](https://www.wikidata.org/wiki/Q112234259) | source type | metaclass of source or origin of object, which could be concrete or abstract |  |
| [Q112807602](https://www.wikidata.org/wiki/Q112807602) | type of social group | social groups | [Types of social groups](https://en.wikipedia.org/wiki/Types_of_social_groups) |
| [Q112872396](https://www.wikidata.org/wiki/Q112872396) | type of educational institution | Wikidata metaclass as a classification for educational institutions |  |
| [Q113355041](https://www.wikidata.org/wiki/Q113355041) | topos theory | area of mathematics dealing with toposes |  |
| [Q114401982](https://www.wikidata.org/wiki/Q114401982) | independent city in Berlin |  |  |
| [Q114955954](https://www.wikidata.org/wiki/Q114955954) | crowdsourced project | project built via crowdsourcing |  |
| [Q115095765](https://www.wikidata.org/wiki/Q115095765) | location | location of something (be it physical, virtual, digital, real or fictional) |  |
| [Q115096159](https://www.wikidata.org/wiki/Q115096159) | sibling project | project that is related to another |  |
| [Q115160940](https://www.wikidata.org/wiki/Q115160940) | mathematical method | method applied to mathematics |  |
| [Q115217689](https://www.wikidata.org/wiki/Q115217689) | server instance | instance of a particular server software |  |
| [Q115431196](https://www.wikidata.org/wiki/Q115431196) | violent conflict | conflict in which physical or psychological violence occurs in some form |  |
| [Q115463072](https://www.wikidata.org/wiki/Q115463072) | Wikibase builtin datatype | datatype that is built into the Wikibase software (as opposed to defined via an extension) |  |
| [Q115470359](https://www.wikidata.org/wiki/Q115470359) | Wikibase item datatype | Wikibase property value datatype |  |
| [Q115471117](https://www.wikidata.org/wiki/Q115471117) | self-depicting entity | entity that depicts or describes itself |  |
| [Q115475104](https://www.wikidata.org/wiki/Q115475104) | Wikibase datatype added by WikibaseLexeme |  |  |
| [Q115490427](https://www.wikidata.org/wiki/Q115490427) | data model element | abstract element of a data model |  |
| [Q115490628](https://www.wikidata.org/wiki/Q115490628) | fundamental Wikidata entity | property or item in Wikidata that allows logical inferences about other properties, items or values in Wikidata to be made and thus enables reasoning about Wikidata in general |  |
| [Q115491417](https://www.wikidata.org/wiki/Q115491417) | description | rhetorical mode to to re-create, invent, or visually present a person, place, event, or action in communication | [Description](https://en.wikipedia.org/wiki/Description) |
| [Q115517465](https://www.wikidata.org/wiki/Q115517465) | computer file location | location where a computer file can reside |  |
| [Q115616700](https://www.wikidata.org/wiki/Q115616700) | W3C Technical Report | technical report published at W3C |  |
| [Q115636432](https://www.wikidata.org/wiki/Q115636432) | labeled directed graph | directed graph where nodes and vertices have labels assigned to them |  |
| [Q115641683](https://www.wikidata.org/wiki/Q115641683) | custodian | person who has responsibility for taking care of or protecting something | [Custodianship](https://en.wikipedia.org/wiki/Custodianship) |
| [Q115642124](https://www.wikidata.org/wiki/Q115642124) | Wikibase Q identifier | identifier for an item in Wikibase, prefixed by a Q |  |
| [Q115660447](https://www.wikidata.org/wiki/Q115660447) | Wikibase instance | server that runs Wikibase |  |
| [Q115668308](https://www.wikidata.org/wiki/Q115668308) | release | unit of realisation of a work or other subject matter intended for the public |  |
| [Q115684393](https://www.wikidata.org/wiki/Q115684393) | RDF vocabulary | collection of IRIs meant to be used in an RDF graph |  |
| [Q115786086](https://www.wikidata.org/wiki/Q115786086) | form | any meaningful unit of speech such as word, phrase, sentence, morpheme or affix |  |
| [Q115820013](https://www.wikidata.org/wiki/Q115820013) | unit of speech | a speech consisting of one uninterrupted vowel sound which may or may not be flanked by one or more consonant sounds; uttered with a single impulse of the voice |  |
| [Q115949945](https://www.wikidata.org/wiki/Q115949945) | scientific concept | concept relating to science |  |
| [Q115988076](https://www.wikidata.org/wiki/Q115988076) | set-valued function | function whose values are sets (mathematics) | [Set-valued function](https://en.wikipedia.org/wiki/Set-valued_function) |
| [Q116457584](https://www.wikidata.org/wiki/Q116457584) | piecewise continuous function |  | [Piecewise continuous](https://en.wikipedia.org/wiki/Piecewise_continuous) |
| [Q116474095](https://www.wikidata.org/wiki/Q116474095) | type of work of art | Wikidata metaclass |  |
| [Q116481801](https://www.wikidata.org/wiki/Q116481801) | type of programming language | Wikidata metaclass |  |
| [Q116505632](https://www.wikidata.org/wiki/Q116505632) | type of process | Wikidata metaclass of process |  |
| [Q116518880](https://www.wikidata.org/wiki/Q116518880) | narrative mode | mode of narrative works in any form - written, oral, visual, etc |  |
| [Q117023459](https://www.wikidata.org/wiki/Q117023459) | type of institution | Wikidata metaclass |  |
| [Q117190471](https://www.wikidata.org/wiki/Q117190471) | sub-fonds | a unit in archival science; subgroup of fonds |  |
| [Q117207263](https://www.wikidata.org/wiki/Q117207263) | file | organized grouping of documents |  |
| [Q117460485](https://www.wikidata.org/wiki/Q117460485) | education and research | activity of nonprofit-organizations |  |
| [Q117747915](https://www.wikidata.org/wiki/Q117747915) | semantic role | role that an entity plays with respect to a specific action or state as part of a coherent scene (i.e. semantic frame). The role may or may not be evoked by a specific lexical item such as a verb. |  |
| [Q118555179](https://www.wikidata.org/wiki/Q118555179) | MediaWiki non-main namespace page | any page within a MediaWiki instance is that resides outside of the main (article) namespace (ns:0) |  |
| [Q119648796](https://www.wikidata.org/wiki/Q119648796) | digital-native publication | a class of publication that originated online |  |
| [Q120721906](https://www.wikidata.org/wiki/Q120721906) | fully faithful functor | functor that is both full and faithful | [Fully faithful functor](https://en.wikipedia.org/wiki/Fully_faithful_functor) |
| [Q121010900](https://www.wikidata.org/wiki/Q121010900) | order-convex set |  | [Order-convex set](https://en.wikipedia.org/wiki/Order-convex_set) |
| [Q121075789](https://www.wikidata.org/wiki/Q121075789) | hemiring | algebraic structure similar to semirings but not necessarily with multiplicative identity |  |
| [Q121132955](https://www.wikidata.org/wiki/Q121132955) | type of mass media | metaclass for mass media |  |
| [Q121344523](https://www.wikidata.org/wiki/Q121344523) | type of classification | Wikidata metaclass for classification of various subjects |  |
| [Q121499459](https://www.wikidata.org/wiki/Q121499459) | submonoid | subset of a monoid containing the identity and closed under the monoid operation | [Submonoid](https://en.wikipedia.org/wiki/Submonoid) |
| [Q121546687](https://www.wikidata.org/wiki/Q121546687) | right adjoint | second of a pair of adjoint functors | [Right adjoint](https://en.wikipedia.org/wiki/Right_adjoint) |
| [Q121771058](https://www.wikidata.org/wiki/Q121771058) | locally small category | category whose morphisms between every two objects form a set |  |
| [Q121773562](https://www.wikidata.org/wiki/Q121773562) | split monomorphism | morphism with a left inverse |  |
| [Q121773569](https://www.wikidata.org/wiki/Q121773569) | split epimorphism | morphism with a right inverse |  |
| [Q121841020](https://www.wikidata.org/wiki/Q121841020) | lexicographic work | broadly, reference works including dictionaries, lexicons, glossaries, vocabulary |  |
| [Q122258005](https://www.wikidata.org/wiki/Q122258005) | abstract reference point | point or level relative to which another point is referenced |  |
| [Q122759350](https://www.wikidata.org/wiki/Q122759350) | user-generated content platform | type of online service that allows its users to upload and share self-created content with other users of the platform |  |
| [Q122764215](https://www.wikidata.org/wiki/Q122764215) | personal risk |  |  |
| [Q123139280](https://www.wikidata.org/wiki/Q123139280) | abstract object | object with no physical referent |  |
| [Q123177423](https://www.wikidata.org/wiki/Q123177423) | object of analysis | any entity being analyzed or evaluated |  |
| [Q123240632](https://www.wikidata.org/wiki/Q123240632) | specifically dependent continuant | BFO class |  |
| [Q123241435](https://www.wikidata.org/wiki/Q123241435) | realizable entity |  |  |
| [Q123345464](https://www.wikidata.org/wiki/Q123345464) | type of interaction | Wikidata metaclass for interaction in various contexts |  |
| [Q123349660](https://www.wikidata.org/wiki/Q123349660) | geolocatable entity | entity that may be assigned mostly stable geographic coordinates and/or geocoded |  |
| [Q123370638](https://www.wikidata.org/wiki/Q123370638) | branch of computer science | Computer Science sub-disciplines |  |
| [Q123407493](https://www.wikidata.org/wiki/Q123407493) | MediaWiki instance | single installation of MediaWiki |  |
| [Q123410745](https://www.wikidata.org/wiki/Q123410745) | geometric object |  | [Geometric object](https://en.wikipedia.org/wiki/Geometric_object) |
| [Q123588392](https://www.wikidata.org/wiki/Q123588392) | type of tool | Wikidata metaclass for tool, equipment, instrument and appliance including physical, virtual, and abstract objects |  |
| [Q123928941](https://www.wikidata.org/wiki/Q123928941) | concern | something that should be considered |  |
| [Q123964505](https://www.wikidata.org/wiki/Q123964505) | populated place | place in which people live, permanently or temporarily |  |
| [Q124222085](https://www.wikidata.org/wiki/Q124222085) | scientific study | any study or project that rigorously expands the limits of knowledge | [Academic study](https://en.wikipedia.org/wiki/Academic_study) |
| [Q124250988](https://www.wikidata.org/wiki/Q124250988) | urban settlement | human settlement with high population density and infrastructure of built environment |  |
| [Q124423945](https://www.wikidata.org/wiki/Q124423945) | 2-groupoid | 2-category in which every 1- and 2-morphism is invertible |  |
| [Q124478208](https://www.wikidata.org/wiki/Q124478208) | liable adult | adult who cares for and is responsible for the actions of one or more children |  |
| [Q124711104](https://www.wikidata.org/wiki/Q124711104) | BFO class | metaclass of all classes defined at some point in time in BFO (“Basic Formal Ontology”) |  |
| [Q125092269](https://www.wikidata.org/wiki/Q125092269) | type of conflict | Wikidata metaclass for conflicts in various situations |  |
| [Q125161275](https://www.wikidata.org/wiki/Q125161275) | type of intelligence | Wikidata metaclass for intelligence or cleverness |  |
| [Q125189273](https://www.wikidata.org/wiki/Q125189273) | library science term | technical term; word or phrase that is part of library science terminology |  |
| [Q125352518](https://www.wikidata.org/wiki/Q125352518) | person with parental authority | parent or other person who holds legal parental power over a minor |  |
| [Q125506646](https://www.wikidata.org/wiki/Q125506646) | transfer | process in which an item associated with one entity becomes similarly associated with another |  |
| [Q125542526](https://www.wikidata.org/wiki/Q125542526) | type of activity | meta class for activity |  |
| [Q125598210](https://www.wikidata.org/wiki/Q125598210) | immaterial entity type |  |  |
| [Q125598382](https://www.wikidata.org/wiki/Q125598382) | independent continuant type |  |  |
| [Q125598647](https://www.wikidata.org/wiki/Q125598647) | continuant type |  |  |
| [Q125684839](https://www.wikidata.org/wiki/Q125684839) | economic capital city | not official title of a city where economy is most active in a country |  |
| [Q127421212](https://www.wikidata.org/wiki/Q127421212) | type of power | Wikidata metaclass for power or ability to influence or direct the actions, beliefs, or conduct of actors |  |
| [Q129586023](https://www.wikidata.org/wiki/Q129586023) | person with an activity |  |  |
| [Q130286945](https://www.wikidata.org/wiki/Q130286945) | type of problem | Wikidata metaclass of problem that presents fundamental challenge or difficulty |  |
| [Q130324710](https://www.wikidata.org/wiki/Q130324710) | type of relation | metaclass for relation or association between different objects, processes or abstractions |  |
| [Q130342754](https://www.wikidata.org/wiki/Q130342754) | labeled mixed graph | vertex- and edge-labeled mixed graph |  |
| [Q130459448](https://www.wikidata.org/wiki/Q130459448) | type of condition | various conditions or certain statuses, be it physical condition, environment, work, or other things |  |
| [Q130583773](https://www.wikidata.org/wiki/Q130583773) | type of crime | Wikimedia metaclass for crime activities |  |
| [Q131085629](https://www.wikidata.org/wiki/Q131085629) | collective agent | an agent who is a gathering or organization of two or more persons that bears a particular name and that is capable of acting as a unit |  |
| [Q131362181](https://www.wikidata.org/wiki/Q131362181) | social science concept | class encompassing concepts used in social science |  |
| [Q131544427](https://www.wikidata.org/wiki/Q131544427) | mental activity | work in which mental energy is used, as opposed to physical work |  |
| [Q132225801](https://www.wikidata.org/wiki/Q132225801) | productive property | mathematical property always fulfilled by the product structure if each factor has it |  |
| [Q132759797](https://www.wikidata.org/wiki/Q132759797) | pedagogic institution | type of institution through pedagogy |  |
| [Q132907471](https://www.wikidata.org/wiki/Q132907471) | individual item | a non-class item, largest first order class |  |
| [Q133449656](https://www.wikidata.org/wiki/Q133449656) | type of work |  |  |
| [Q133873821](https://www.wikidata.org/wiki/Q133873821) | academic organisation | type of organization for academia |  |
| [Q133873855](https://www.wikidata.org/wiki/Q133873855) | research institution | type of institution |  |
| [Q134261520](https://www.wikidata.org/wiki/Q134261520) | group or class of humans | second-order class of humans |  |
| [Q134264207](https://www.wikidata.org/wiki/Q134264207) | class of human | collection of humans defined by common characteristics |  |
| [Q134445478](https://www.wikidata.org/wiki/Q134445478) | cultural capital |  |  |
| [Q134480019](https://www.wikidata.org/wiki/Q134480019) | proto-agent | semantic label for the most agent-like argument - something that acts or is treated like it performs actions, even if it can't consciously or intentionally do so |  |
| [Q134487654](https://www.wikidata.org/wiki/Q134487654) | relational structure | model-theoretical structure which consists of a set and a family of finitary relations |  |
| [Q134488202](https://www.wikidata.org/wiki/Q134488202) | possibly infinitary structure | generalization of structure which allows infinitary operations and relations |  |
| [Q134601727](https://www.wikidata.org/wiki/Q134601727) | group of persons | any set of beings with personhood (for groups of humans, use Q16334295 [group of humans] with P31 [instance of]) |  |
| [Q134601860](https://www.wikidata.org/wiki/Q134601860) | class of person | collection of beings with personhood defined by common characteristics |  |
| [Q134601875](https://www.wikidata.org/wiki/Q134601875) | group or class of people | second-order class of people (beings with personhood) |  |
| [Q134602505](https://www.wikidata.org/wiki/Q134602505) | group of beings | any set of entities with agency |  |
| [Q134602526](https://www.wikidata.org/wiki/Q134602526) | group or class of beings | second-order class of entities with agency |  |
| [Q134602570](https://www.wikidata.org/wiki/Q134602570) | class of being | collection of entities with agency defined by common characteristics |  |
| [Q134995802](https://www.wikidata.org/wiki/Q134995802) | type of website | type of website, denoting the form and specificity of the website |  |
| [Q135265559](https://www.wikidata.org/wiki/Q135265559) | group of 3 | generic group of three things |  |
| [Q135268423](https://www.wikidata.org/wiki/Q135268423) | generic set | set of n generic things, as opposed to a concrete number which is a set of specific things |  |
| [Q135268494](https://www.wikidata.org/wiki/Q135268494) | group of 2 | generic group of 2 things |  |
| [Q135268496](https://www.wikidata.org/wiki/Q135268496) | group of 4 | generic group of 4 things |  |
| [Q135268497](https://www.wikidata.org/wiki/Q135268497) | Group of 5 | A generic group of 5 things |  |
| [Q135268502](https://www.wikidata.org/wiki/Q135268502) | Group of 8 | A generic group of 8 things |  |
| [Q135412187](https://www.wikidata.org/wiki/Q135412187) | resource type | metaclass of resource, which could be natural, social or technical |  |
| [Q135457975](https://www.wikidata.org/wiki/Q135457975) | computable complex number | complex number whose real and imaginary parts are computable |  |
| [Q135457986](https://www.wikidata.org/wiki/Q135457986) | definable complex number | complex number whose real and imaginary parts are definable |  |
| [Q135899674](https://www.wikidata.org/wiki/Q135899674) | application-specific graph | graph used as a model for a purpose outside of graph theory |  |
| [Q136375263](https://www.wikidata.org/wiki/Q136375263) | Wikimedia multilingual project | Wikimedia project that handle multiple languages with in-wiki translation |  |
| [Q136410232](https://www.wikidata.org/wiki/Q136410232) | research organization | type of organization for doing research |  |
| [Q136433633](https://www.wikidata.org/wiki/Q136433633) | wiki genre | category of wikis |  |
| [Q136433660](https://www.wikidata.org/wiki/Q136433660) | entity | BFO class |  |
| [Q136772242](https://www.wikidata.org/wiki/Q136772242) | type of living thing | metaclass |  |
| [Q136873419](https://www.wikidata.org/wiki/Q136873419) | birth mother | person who gave birth to the child (genetic mother, mother using donated egg or embryo, as well as gestational surrogate), recognized as default legal parent in many jurisdictions |  |
| [Q136875493](https://www.wikidata.org/wiki/Q136875493) | gestational surrogacy | when a woman agrees to carry a child not concieved with her own eggs for a third party |  |
| [Q136937144](https://www.wikidata.org/wiki/Q136937144) | project type | project type classification; kind of project |  |
| [Q137015716](https://www.wikidata.org/wiki/Q137015716) | type of location | second-order class of location |  |
| [Q137018865](https://www.wikidata.org/wiki/Q137018865) | type of place | second order class of place |  |
| [Q137022846](https://www.wikidata.org/wiki/Q137022846) | type of region | second order class of region |  |
| [Q137023128](https://www.wikidata.org/wiki/Q137023128) | region | first order class of region. Things known as regions. |  |
| [Q137425179](https://www.wikidata.org/wiki/Q137425179) | type of good | metaclass for goods |  |
| [Q137426749](https://www.wikidata.org/wiki/Q137426749) | type of term | metaclass for term |  |
| [Q137428550](https://www.wikidata.org/wiki/Q137428550) | type of terminology | metaclass for terminology |  |
| [Q137429456](https://www.wikidata.org/wiki/Q137429456) | type of concept | metaclass for concepts |  |
| [Q137527772](https://www.wikidata.org/wiki/Q137527772) | type of computer language | metaclass |  |
| [Q137774087](https://www.wikidata.org/wiki/Q137774087) | type of violence | metaclass for violence |  |
| [Q138012087](https://www.wikidata.org/wiki/Q138012087) | type of standard |  |  |
| [Q138303935](https://www.wikidata.org/wiki/Q138303935) | type of information | metaclass for kinds of information |  |
| [Q138579261](https://www.wikidata.org/wiki/Q138579261) | type of calendar | Wikidata metaclass |  |
| [Q138589449](https://www.wikidata.org/wiki/Q138589449) | core branches of philosophy | subdivision of the field of philosophy in core branches |  |
| [Q138665581](https://www.wikidata.org/wiki/Q138665581) | type of set | metaclass for classes of sets |  |
| [Q138715303](https://www.wikidata.org/wiki/Q138715303) | older relative | relative who is of a greater chronological age |  |
| [Q138715847](https://www.wikidata.org/wiki/Q138715847) | senior relative | relative who belongs to an earlier genealogical generation, someone situated higher up on a family tree (regardless of chronological age) |  |
| [Q138715965](https://www.wikidata.org/wiki/Q138715965) | peer relative | relative who belongs to the same genealogical generation, someone situated on the same level on a family tree (regardless of chronological age) |  |
| [Q138716141](https://www.wikidata.org/wiki/Q138716141) | non-peer relative | relative who belongs to a different genealogical generation, someone situated on a higher or lower level on a family tree (regardless of chronological age) |  |
| [Q138716757](https://www.wikidata.org/wiki/Q138716757) | sibling or peer cousin | kinship (found in for example Hawaiian kinship systems) |  |
| [Q138716795](https://www.wikidata.org/wiki/Q138716795) | parent or peer relative of parent | kinship in the Hawaiian kinship system |  |
| [Q138716859](https://www.wikidata.org/wiki/Q138716859) | mother or mother's sister | kinship (found in for example Iroquois kinship systems) |  |
| [Q138717307](https://www.wikidata.org/wiki/Q138717307) | sibling or parallel cousin | kinship (found in for example Iroquois kinship systems) |  |
| [Q139243747](https://www.wikidata.org/wiki/Q139243747) | type of artifact | metaclass for artifacts (artificial objects including intellectual works) |  |
| [Q139338152](https://www.wikidata.org/wiki/Q139338152) | informal mathematical concept | concept in mathematics with no widely accpeted precise definition |  |
| [Q139761564](https://www.wikidata.org/wiki/Q139761564) | Cubical type theory |  | [Cubical type theory](https://en.wikipedia.org/wiki/Cubical_type_theory) |
| [Q140156619](https://www.wikidata.org/wiki/Q140156619) | continuous functor | functor which preserves small limits | [Continuous functor](https://en.wikipedia.org/wiki/Continuous_functor) |
| [Q140311475](https://www.wikidata.org/wiki/Q140311475) | type of creative work |  |  |
| [Q140354053](https://www.wikidata.org/wiki/Q140354053) | type of series |  |  |
| [Q140354262](https://www.wikidata.org/wiki/Q140354262) | type of genre |  |  |
| [Q140437324](https://www.wikidata.org/wiki/Q140437324) | type of state | 2nd order class of states of object/s |  |
| [Q140451665](https://www.wikidata.org/wiki/Q140451665) | event | spatiotemporal entity/entities that may have (an) associated occurrence/s or planned occurrence and/or related objects |  |
| [Q140458154](https://www.wikidata.org/wiki/Q140458154) | type of abstract object | second-order class of abstract objects by type |  |
| [Q140639962](https://www.wikidata.org/wiki/Q140639962) | type of behavior | type, form or class of behavior;characterization of behavior/s |  |
| [Q140642100](https://www.wikidata.org/wiki/Q140642100) | type of model | type or class of model |  |
| [Q140914670](https://www.wikidata.org/wiki/Q140914670) | monadic functor | right adjoint whose comparison functor is an equivalence of categories |  |
| [Q140919303](https://www.wikidata.org/wiki/Q140919303) | region | region in a dimensional space; value for a quality of an entity |  |
| [Q141000153](https://www.wikidata.org/wiki/Q141000153) | passive interaction |  |  |
| [Q141000803](https://www.wikidata.org/wiki/Q141000803) | active interaction |  |  |
| [Q141004607](https://www.wikidata.org/wiki/Q141004607) | material change |  |  |
| [Q141066018](https://www.wikidata.org/wiki/Q141066018) | semifunctor |  |  |
| [Q141066057](https://www.wikidata.org/wiki/Q141066057) | functor that reflects limits | functor for which a cone is a limit whenever its image under the functor is |  |
| [Q141066058](https://www.wikidata.org/wiki/Q141066058) | functor that creates limits | functor that lifts and reflects limits |  |
| [Q141066060](https://www.wikidata.org/wiki/Q141066060) | functor that lifts limits | functor for which every limiting cone arises as the image of another limiting cone |  |
