/-!
Comparative Marxian revolutionary translation family.

Selected cases: Iran, Vietnam, China, Algeria, Nicaragua, South Africa.
The construction compares local translation of Marxian/Leninist relations
without ranking cases or identifying one revolution with another.
-/

namespace AgdaMirror.Governance.ComparativeMarxianRevolutionaryTranslationFamily

inductive RevolutionaryCase
  | iran | vietnam | china | algeria | nicaragua | southAfrica
  deriving DecidableEq, Repr

structure RevolutionaryTranslationProfile where
  case : RevolutionaryCase
  sourceReceipt : String
  revolutionarySubject : String
  nationalFrame : String
  classCoalition : String
  peasantRole : String
  religiousOrNormativeTranslation : String
  colonialRacialRelation : String
  stateBuildingRelation : String
  internationalismRelation : String
  pluralityResidual : String
  marxianGrammarPresent : Bool := true
  localTranslationPresent : Bool := true
  translationEqualsOrthodoxMarxism : Bool := false
  oneCaseDeterminesAnother : Bool := false
  caseRankingCreated : Bool := false

def iranProfile : RevolutionaryTranslationProfile :=
  ⟨.iran,
   "Iranian revolutionary genealogy and Shariati/Khomeini owners",
   "mostazafin/oppressed subject plus Islamic revolutionary constituency",
   "anti-imperialist sovereignty and Islamic revolutionary order",
   "class grammar translated into a wider oppressed/oppressor field",
   "not sole revolutionary subject",
   "Shi'i political theology and Islamic-humanist revolutionary ontology",
   "anti-colonial / anti-hegemonic relation",
   "jurist-led Islamic state; not proletarian sovereignty",
   "solidarity of oppressed / resistance field",
   "Marxian, Islamic, nationalist and Third-Worldist strands remain distinct"⟩

def vietnamProfile : RevolutionaryTranslationProfile :=
  ⟨.vietnam,
   "Fadaee 2026; Red Internationalism 2023; McHale 2010",
   "workers-and-peasants bloc with peasantry fundamental in local conditions",
   "national independence joined to communist revolution",
   "Leninist two-stage strategy plus coalition-building",
   "fundamental revolutionary role in a predominantly peasant society",
   "national and inherited cultural contexts remain historical residuals",
   "French colonial domination and later anti-imperialist struggle",
   "national liberation followed by communist state-building",
   "Leninist self-determination in tension with universal communist emancipation",
   "Vietnamese Marxism remains non-monolithic"⟩

def chinaProfile : RevolutionaryTranslationProfile :=
  ⟨.china,
   "Wylie on Sinification; Cambridge History peasant movements",
   "party-army / peasant-centred revolutionary mobilisation",
   "Chinese national and revolutionary transformation",
   "Marxism-Leninism adapted to agrarian conditions",
   "central rather than auxiliary",
   "Chinese historical inheritance retained as translation context",
   "semi-colonial / imperial domination and landlord relations",
   "party-state construction after revolutionary victory",
   "international Marxism translated into Chinese conditions",
   "adaptation and rupture remain visible"⟩

def algeriaProfile : RevolutionaryTranslationProfile :=
  ⟨.algeria,
   "Mackinnon 2023 plus Fanon source lane",
   "colonised national subject and liberation movement",
   "anti-colonial national liberation",
   "class analysis intersects coloniser/colonised relation",
   "rural and colonised masses not reduced to European proletarian model",
   "Fanonian humanism and anti-colonial political thought",
   "French colonial domination",
   "postcolonial state-building remains distinct downstream problem",
   "Third-World anti-colonial internationalism",
   "Fanon and FLN-related thought not collapsed into one doctrine"⟩

def nicaraguaProfile : RevolutionaryTranslationProfile :=
  ⟨.nicaragua,
   "Jarquín 2021",
   "plural anti-Somoza revolutionary coalition",
   "national revolution",
   "Marxist-Leninist strands coexist with other constituencies",
   "case-specific popular mobilisation",
   "liberation theology coexists with Marxist and social-democratic currents",
   "dictatorship, inequality and external intervention",
   "revolutionary government and survival under external pressure",
   "Cuban and wider revolutionary international connections",
   "FSLN leaders differed over Marxism's applicability"⟩

def southAfricaProfile : RevolutionaryTranslationProfile :=
  ⟨.southAfrica,
   "McKinley on ANC Marxism",
   "racially oppressed national majority with asserted working-class leadership",
   "national democratic revolution",
   "multi-class revolutionary front",
   "not primary defining axis",
   "national-democratic and Marxist registers coexist",
   "colonial dispossession plus racialised capitalism",
   "nation-building without automatic socialist transition",
   "anti-colonial / socialist internationalism",
   "national liberation and socialism remain related but non-identical horizons"⟩

def canonicalProfiles : List RevolutionaryTranslationProfile :=
  [iranProfile, vietnamProfile, chinaProfile, algeriaProfile, nicaraguaProfile, southAfricaProfile]

theorem all_selected_cases_are_local_translations :
    ∀ p ∈ canonicalProfiles,
      p.marxianGrammarPresent = true ∧
      p.localTranslationPresent = true ∧
      p.translationEqualsOrthodoxMarxism = false ∧
      p.oneCaseDeterminesAnother = false ∧
      p.caseRankingCreated = false := by
  intro p h
  simp [canonicalProfiles] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end AgdaMirror.Governance.ComparativeMarxianRevolutionaryTranslationFamily
