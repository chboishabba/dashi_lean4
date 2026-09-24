#!/usr/bin/env bash
# Rebuilds the whole corpus: query Wikidata, import the facts, merge them, and
# compile everything to Lean modules under RequestProject/Generated/.
#
#   scripts/refresh-corpus.sh            # download what is not cached
#   scripts/refresh-corpus.sh --offline  # rebuild from the cache only
#
# Downloads are cached in .wikidata-cache/, so a second run needs no network.
# The .wdkb files under data/ and the Lean modules under RequestProject/Generated/
# are the outputs; both are checked into the repository.
set -e
cd "$(dirname "$0")/.."
lake build wikidata
WD=./.lake/build/bin/wikidata
OFFLINE="${1:-}"
mkdir -p data

echo "== 1. query Wikidata =="

$WD fetch Q42 --depth 2 $OFFLINE --quiet --no-warn \
    --name "douglas-adams" --out data/douglas.wdkb | tail -1

$WD fetch Q35120 Q16889133 Q19478619 Q24017414 Q24017465 Q104054982 Q23958946 \
         Q99527517 Q488383 Q4406616 Q7184903 --depth 2 $OFFLINE --quiet --no-warn \
    --name "wikidata-upper-ontology" --out data/upper.wdkb | tail -1

$WD fetch Q515 Q6256 Q3624078 Q486972 Q56061 Q82794 Q2221906 Q64 Q90 Q30 \
         --depth 2 $OFFLINE --quiet --no-warn \
    --name "geography" --out data/geography.wdkb | tail -1

$WD fetch Q11424 Q571 Q7725634 Q386724 Q838948 Q2188189 Q25169 Q42 \
         --depth 2 $OFFLINE --quiet --no-warn \
    --name "creative-works" --out data/creative.wdkb | tail -1

$WD fetch Q937 Q1035 Q7259 Q901 Q11862829 Q336 --depth 2 $OFFLINE --quiet --no-warn \
    --name "science" --out data/science.wdkb | tail -1

$WD fetch Q7397 Q68 Q9143 Q28865 Q11660 Q80006 --depth 2 $OFFLINE --quiet --no-warn \
    --name "technology" --out data/technology.wdkb | tail -1

$WD fetch Q395 Q65943 Q11348 Q12503 Q1936384 --depth 2 $OFFLINE --quiet --no-warn \
    --name "mathematics" --out data/mathematics.wdkb | tail -1

$WD fetch Q7239 Q16521 Q729 Q756 Q7187 Q8054 --depth 2 $OFFLINE --quiet --no-warn \
    --name "life-sciences" --out data/life.wdkb | tail -1

$WD fetch Q43229 Q4830453 Q3918 Q7278 Q327333 Q28640 --depth 2 $OFFLINE --quiet --no-warn \
    --name "society" --out data/society.wdkb | tail -1

$WD fetch Q11344 Q11173 Q79529 Q12136 Q8386 Q11367 --depth 2 $OFFLINE --quiet --no-warn \
    --name "chemistry-medicine" --out data/chemistry.wdkb | tail -1

$WD fetch Q1190554 Q1656682 Q198 Q13418847 Q186081 Q1914636 --depth 2 $OFFLINE --quiet --no-warn \
    --name "events" --out data/events.wdkb | tail -1

# The mathematical notions this development is itself made of: the Wikidata
# articles that `RequestProject/Vocabulary.lean` matches with the constructions
# of the library, and `RequestProject/MathResonance.lean` proves it instantiates.
# This fragment is about the *notions*, not about a domain, so it is compiled on
# its own and deliberately left out of the merged core corpus below.
$WD fetch Q215111 Q208237 Q11077412 Q1425985 Q1397439 Q1322614 Q1417809 Q621542 Q2141963 \
         Q44106280 Q217608 Q864213 Q357858 Q48998319 Q381060 Q182003 Q229102 Q180907 \
         Q189112 Q368988 Q130998 Q3966112 Q338021 Q430001 Q693083 Q15846555 \
         Q6134913 Q42866132 Q54980267 Q1609475 Q1308999 Q1137726 \
         --depth 2 $OFFLINE --quiet --no-warn \
    --name "mathematical-structures" --out data/structures.wdkb | tail -1

# The frontier of the crawls above: every item the corpus mentions but says
# nothing about, asked one step further.  These are exactly the items that had
# no `subclass of` / `instance of` statement in data/core.wdkb.
$WD fetch \
        Q111513007 Q19798651 Q24027526 Q77730568 Q48907157 Q8425 Q33104129 Q61961344  \
        Q125598210 Q82799 Q836915 Q15631850 Q1418640 Q41773366 Q4057633 Q3268571 Q15042037  \
        Q1907114 Q15284 Q163359 Q16003513 Q1799794 Q192498 Q837766 Q56427813 Q123705  \
        Q16334295 Q659390 Q15239622 Q19953632 Q19832712 Q5589178 Q2752458 Q28108 Q28877  \
        Q137425179 Q64513524 Q8963063 Q3523102 Q1554231 Q135412187 Q20936777 Q135268497  \
        Q6630149 Q29428403 Q17538690 Q2217301 Q28062188 Q7725310 Q140354053 Q72638  \
        Q134601860 Q15978631 Q134264207 Q1914017 Q3400985 Q795052 Q13406463 Q1531349  \
        Q15851373 Q627436 Q483394 Q141000803 Q125542526 Q28813620 Q1485500 Q649732  \
        Q66664364 Q28923954 Q8366 Q1260632 Q475023 Q34104 Q781413 Q853614 Q2145290 Q1980247  \
        Q55915575 Q12042160 Q591041 Q36161 Q107223533 Q1321926 Q12916 Q646245 Q68023621  \
        Q11567 Q11563 Q379825 Q1979154 Q103812671 Q103997018 Q103940464 Q136772242 Q1454986  \
        Q6671777 Q16686022 Q169336 Q214609 Q2393187 Q355679 Q123139280 Q11028 Q12488383  \
        Q1207505 Q2169973 Q132759797 Q178706 Q136410232 Q5341295 Q48937186 Q3695082 Q895526  \
        Q714737 Q115491417 Q6005984 Q3505845 Q813912 Q122764215 Q1132455 Q101208084 Q483247  \
        Q1322005 Q111752858 Q1293220 Q2995644 Q24249534 Q125506646 Q2976602 Q131362181  \
        Q24902509 Q115431196 Q2141565 Q123928941 Q68482296 Q839578 Q86923152 Q12558574  \
        Q4897819 Q127244 Q138665581 Q179899 Q132225801 Q177646 \
         --depth 1 $OFFLINE --quiet --no-warn \
    --name "frontier" --out data/frontier.wdkb | tail -1

# The same question asked again of the corpus extended by the fragment above:
# the items it in turn mentions without saying anything about them.
$WD fetch \
        Q16003513 Q14946528 Q125598647 Q100320664 Q789016 Q82042 Q699386 Q101072 Q783794  \
        Q7188 Q4358176 Q16334298 Q134602505 Q15893266 Q12046615 Q1084 Q803935 Q66707394  \
        Q726212 Q309314 Q47574 Q107715 Q635162 Q129586023 Q134480019 Q4330518 Q2085518  \
        Q15633587 Q191067 Q17379835 Q118555179 Q8242 Q109551565 Q108329096 Q223393  \
        Q108466143 Q10383930 Q1851710 Q3893614 Q135457975 Q29428373 Q743418 Q135268494  \
        Q600590 Q36808958 Q103994247 Q908049 Q28877390 Q22675015 Q3685323 Q71574018  \
        Q19885597 Q1415187 Q2198779 Q367293 Q35758 Q21170479 Q9492 Q111931734 Q12379553  \
        Q191797 Q60971579 Q2515887 Q137774087 Q602884 Q921513 Q613930 Q123240632 Q4833865  \
        Q64861 \
         --depth 1 $OFFLINE --quiet --no-warn \
    --name "frontier-round-2" --out data/frontier2.wdkb | tail -1

# The notions `RequestProject/Vocabulary.lean` names but that no earlier
# download had covered.
$WD fetch Q2013 Q11398 Q31184 Q54872 Q157509 Q171318 Q185359 Q185837 Q186408 Q188619 Q194404 \
         Q215382 Q223973 Q324254 Q374182 Q402152 Q467606 Q593744 Q753127 Q774347 Q1129622 \
         Q1182260 Q1189753 Q1194916 Q1195339 Q1217379 Q1224764 Q1266546 Q1361526 Q1437394 \
         Q1491747 Q1501387 Q1502246 Q1781706 Q1985727 Q1985786 Q2362924 Q2427941 Q2996729 \
         Q3088151 Q3306762 Q3539534 Q3882785 Q4312352 Q10564851 Q12338229 Q16222597 Q16547118 \
         Q17587456 Q18616576 Q18647515 Q18647518 Q19798647 Q19798648 Q19822352 Q19847637 \
         Q20746742 Q21044622 Q21503250 Q21510865 Q29377880 Q43649390 Q44292661 Q44292881 \
         Q51885771 Q54285143 Q54285715 Q66363655 Q71533031 Q73737153 Q73737357 Q93447297 \
         Q105770631 Q107659597 Q107659723 Q107659784 Q136873419 \
         --depth 2 $OFFLINE --quiet --no-warn \
    --name "vocabulary-notions" --out data/vocabulary.wdkb | tail -1

# The structures next door: the notions the later layers of the library needed,
# matched with declarations in `RequestProject/RelatedNotions.lean`.
$WD fetch Q7241077 Q595298 Q1442189 Q868169 Q603880 Q1147242 Q1945067 Q1347208 Q1148924 \
         Q5569420 Q202906 Q1082992 Q2646117 Q91432273 Q10535634 Q7098616 Q320577 Q1467124 \
         Q1154996 Q2547089 --depth 2 $OFFLINE --quiet --no-warn \
    --name "related-structures" --out data/related.wdkb | tail -1

# Rounds three and four of the same question, asked of the corpus each earlier
# round produced.  The frontier shrinks 144 -> 70 -> 42 -> 18 -> 14.
$WD fetch \
        Q1000660 Q111279923 Q111667622 Q12050496 Q135268496 Q135268502 Q1456832 Q16003513  \
        Q1621273 Q1747121 Q1759104 Q19798642 Q212434 Q21281405 Q22269697 Q22299433 Q230855  \
        Q2574811 Q259590 Q2835957 Q2944660 Q3257782 Q3307145 Q33104303 Q3533467 Q35798  \
        Q36774 Q378078 Q38885242 Q3958441 Q4184950 Q4391941 Q474715 Q56512863 Q576639  \
        Q595364 Q64588497 Q7377 Q76272846 Q83267 Q93468132 Q96634632  \
         --depth 1 $OFFLINE --quiet --no-warn \
    --name "frontier-round-3" --out data/frontier3.wdkb | tail -1

$WD fetch \
        Q10567583 Q10915 Q110854677 Q115490427 Q115820013 Q1209283 Q1292333 Q1348645  \
        Q16003513 Q161172 Q17006903 Q18848 Q192276 Q20026918 Q2101636 Q2305441 Q694975  \
        Q7233031  \
         --depth 1 $OFFLINE --quiet --no-warn \
    --name "frontier-round-4" --out data/frontier4.wdkb | tail -1

# The categorical structures the later layers of the library use and the first
# batch of related structures had missed.
$WD fetch Q5140810 Q1633079 Q1780005 Q7631737 Q692689 Q2007878 Q1945014 Q1224487 Q2143621 \
         Q1725874 Q1575634 Q113355041 --depth 2 $OFFLINE --quiet --no-warn \
    --name "related-structures-round-2" --out data/related2.wdkb | tail -1

# The family Wikidata itself belongs to: the vocabulary of knowledge
# representation, which no earlier download had covered.
$WD fetch Q387196 Q826165 Q1751819 Q2288360 Q54871 Q3929429 Q7095059 Q1469824 Q17152639 \
         Q1045785 Q2903989 Q837495 --depth 2 $OFFLINE --quiet --no-warn \
    --name "knowledge-representation" --out data/knowledge.wdkb | tail -1

echo
echo "== 2. merge the fragments into one corpus =="
$WD merge data/douglas.wdkb data/upper.wdkb data/geography.wdkb \
          data/creative.wdkb data/science.wdkb data/technology.wdkb data/mathematics.wdkb \
          data/life.wdkb data/society.wdkb data/chemistry.wdkb data/events.wdkb \
    --dedup --infer-levels --name "wikidata-core" --out data/core.wdkb --no-warn \
  | grep -v "✗"

echo
echo "== 3. compile everything to Lean =="
# The two small fragments are checked by the kernel; the large ones by compiled
# evaluation (`native_decide`), which is what makes them feasible.
$WD lean data/douglas.wdkb   --module RequestProject.Generated.DouglasAdams  --kernel --highlights 6 $OFFLINE
$WD lean data/upper.wdkb     --module RequestProject.Generated.UpperOntology --kernel --highlights 6 $OFFLINE
$WD lean data/geography.wdkb --module RequestProject.Generated.Geography     --highlights 6 $OFFLINE
$WD lean data/creative.wdkb  --module RequestProject.Generated.CreativeWorks --highlights 6 $OFFLINE
$WD lean data/science.wdkb   --module RequestProject.Generated.Science       --highlights 6 $OFFLINE
$WD lean data/technology.wdkb --module RequestProject.Generated.Technology   --highlights 6 $OFFLINE
$WD lean data/mathematics.wdkb --module RequestProject.Generated.Mathematics --highlights 6 $OFFLINE
$WD lean data/life.wdkb      --module RequestProject.Generated.LifeSciences  --highlights 6 $OFFLINE
$WD lean data/society.wdkb   --module RequestProject.Generated.Society       --highlights 6 $OFFLINE
$WD lean data/chemistry.wdkb --module RequestProject.Generated.Chemistry     --highlights 6 $OFFLINE
$WD lean data/events.wdkb    --module RequestProject.Generated.Events        --highlights 6 $OFFLINE
$WD lean data/structures.wdkb --module RequestProject.Generated.Structures    --highlights 6 $OFFLINE
$WD lean data/core.wdkb      --module RequestProject.Generated.Core          --highlights 6 $OFFLINE
$WD lean data/frontier.wdkb  --module RequestProject.Generated.Frontier      --highlights 6 $OFFLINE
$WD lean data/frontier2.wdkb --module RequestProject.Generated.Frontier2     --highlights 6 $OFFLINE
$WD lean data/vocabulary.wdkb --module RequestProject.Generated.VocabularyCorpus --highlights 6 $OFFLINE
$WD lean data/related.wdkb   --module RequestProject.Generated.RelatedStructures --highlights 6 $OFFLINE
$WD lean data/frontier3.wdkb --module RequestProject.Generated.Frontier3     --highlights 6 $OFFLINE
$WD lean data/frontier4.wdkb --module RequestProject.Generated.Frontier4     --highlights 6 $OFFLINE
$WD lean data/related2.wdkb  --module RequestProject.Generated.RelatedStructures2 --highlights 6 $OFFLINE
$WD lean data/knowledge.wdkb --module RequestProject.Generated.KnowledgeRepresentation --highlights 6 $OFFLINE

echo
echo "== 4. let Lean re-check the compiled facts =="
lake build
