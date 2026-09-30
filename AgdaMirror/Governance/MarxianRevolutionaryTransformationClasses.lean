import AgdaMirror.Governance.ComparativeMarxianRevolutionaryTranslationFamily

namespace AgdaMirror.Governance.MarxianRevolutionaryTransformationClasses

open AgdaMirror.Governance.ComparativeMarxianRevolutionaryTranslationFamily

inductive TransformationClass
  | agrarianisation | nationalisation | religiousTranslation
  | racialColonialRecoding | multiClassCoalition
  | antiImperialistInternationalisation | postVictoryStateTransformation
  | ideologicalPluralisation | sovereigntyReframing
  deriving DecidableEq, Repr

structure TransformationWitness where
  case : RevolutionaryCase
  transform : TransformationClass
  sourceProfile : RevolutionaryTranslationProfile
  reading : String
  exhaustiveOfCase : Bool := false
  impliesOrthodoxIdentity : Bool := false
  createsCaseRanking : Bool := false

def iranReligiousTranslation : TransformationWitness :=
  ⟨.iran, .religiousTranslation, iranProfile,
   "Marxian/Third-Worldist antagonism reworked through Shi'i political theology."⟩

def vietnamAgrarianisation : TransformationWitness :=
  ⟨.vietnam, .agrarianisation, vietnamProfile,
   "Leninist strategy adapted to a peasant-majority anti-colonial formation."⟩

def chinaAgrarianisation : TransformationWitness :=
  ⟨.china, .agrarianisation, chinaProfile,
   "Sinification adapts Marxism-Leninism to Chinese agrarian conditions."⟩

def algeriaColonialRecoding : TransformationWitness :=
  ⟨.algeria, .racialColonialRecoding, algeriaProfile,
   "Class relation intersects coloniser/colonised relation."⟩

def nicaraguaPluralisation : TransformationWitness :=
  ⟨.nicaragua, .ideologicalPluralisation, nicaraguaProfile,
   "Marxist-Leninist, liberation-theology and social-democratic currents coexist."⟩

def southAfricaCoalition : TransformationWitness :=
  ⟨.southAfrica, .multiClassCoalition, southAfricaProfile,
   "Marxist analysis embedded in a multi-class national-democratic strategy."⟩

def canonicalWitnesses : List TransformationWitness :=
  [iranReligiousTranslation, vietnamAgrarianisation, chinaAgrarianisation,
   algeriaColonialRecoding, nicaraguaPluralisation, southAfricaCoalition]

theorem all_witnesses_nonexhaustive_nonranking :
    ∀ w ∈ canonicalWitnesses,
      w.exhaustiveOfCase = false ∧
      w.impliesOrthodoxIdentity = false ∧
      w.createsCaseRanking = false := by
  intro w h
  simp [canonicalWitnesses] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end AgdaMirror.Governance.MarxianRevolutionaryTransformationClasses
