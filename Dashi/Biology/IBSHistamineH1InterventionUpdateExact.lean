import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.IBSHistamineH1InterventionUpdateExact
open Dashi.Biology.GABAPhenotypeEvidenceExact

def decraecker2024Source : AttributedSource :=
  mkDOISource
    "Lisse Decraecker; Danny De Looze; David P Hirsch; Heiko De Schepper; Joris Arts; Philip Caenepeel; Albert J Bredenoord; Jeroen Kolkman; Koen Bellens; Kim Van Beek; Fedrica Pia; Willy Peetermans; Tim Vanuytsel; Alexandre Denadai-Souza; Ann Belmans; Guy Boeckxstaens"
    "Treatment of non-constipated irritable bowel syndrome with the histamine 1 receptor antagonist ebastine: a randomised, double-blind, placebo-controlled trial"
    "Gut 73(3):459-469" "2024"
    "10.1136/gutjnl-2023-331634" "https://doi.org/10.1136/gutjnl-2023-331634"
    "Multicentre randomized placebo-controlled phase-2 H1-antagonist evidence in non-constipated IBS; composite responder endpoint favored ebastine while individual endpoints did not reach conventional significance."

def pia2026Source : AttributedSource :=
  mkDOISource
    "Fedrica Pia; Lisse Decraecker; Danny De Looze; David Hirsch; Heiko De Schepper; Joris Arts; Philip Caenepeel; Albert J Bredenoord; Tim Vanuytsel; Ann Belmans; Guy E Boeckxstaens"
    "Dose-Dependent Effect of the Histamine 1 Receptor Antagonist Ebastine in Patients With Non-Constipated Irritable Bowel Syndrome"
    "Neurogastroenterology & Motility 38(1):e70242" "2026"
    "10.1111/nmo.70242" "https://doi.org/10.1111/nmo.70242"
    "Open-label 40-vs-20 mg comparison reporting more abdominal-pain responders and lower diarrhea severity at 40 mg; not a randomized placebo-controlled dose trial."

inductive InterventionDesign where
  | randomizedDoubleBlindPlaceboControlled | openLabelDoseComparison
  deriving Repr, DecidableEq

structure H1InterventionReceipt where
  source : AttributedSource
  design : InterventionDesign
  nonConstipatedIBSPopulation : Bool
  h1AntagonistIntervention : Bool
  painOrGlobalSymptomEndpoint : Bool
  placeboCausalContrastPaid : Bool
  doseComparisonPaid : Bool
  boundary : String
  deriving Repr, DecidableEq

def decraecker2024Receipt : H1InterventionReceipt := {
  source := decraecker2024Source
  design := .randomizedDoubleBlindPlaceboControlled
  nonConstipatedIBSPopulation := true
  h1AntagonistIntervention := true
  painOrGlobalSymptomEndpoint := true
  placeboCausalContrastPaid := true
  doseComparisonPaid := false
  boundary := "Composite endpoint retained as reported; not rewritten as significance of each component endpoint."
}

def pia2026Receipt : H1InterventionReceipt := {
  source := pia2026Source
  design := .openLabelDoseComparison
  nonConstipatedIBSPopulation := true
  h1AntagonistIntervention := true
  painOrGlobalSymptomEndpoint := true
  placeboCausalContrastPaid := false
  doseComparisonPaid := true
  boundary := "Open-label dose evidence does not manufacture a placebo-controlled causal dose-response theorem."
}

inductive OpenLabelEqualsRandomizedPlaceboContrastPermission : Prop
inductive H1BenefitIdentifiesAllIBSAsHistamineDrivenPermission : Prop

theorem openLabelDoesNotEqualRandomizedPlaceboContrast : OpenLabelEqualsRandomizedPlaceboContrastPermission → False := by intro h; cases h
theorem h1BenefitDoesNotIdentifyAllIBSAsHistamineDriven : H1BenefitIdentifiesAllIBSAsHistamineDrivenPermission → False := by intro h; cases h

structure IBSHistamineH1InterventionBoundary where
  randomizedH1InterventionEvidenceAcquired : Bool
  openLabelDoseEvidenceAcquired : Bool
  designsCollapsed : Bool
  allIBSHistamineDrivenClaimed : Bool
  quailEfficacyPaidByTheseTrials : Bool
  deriving Repr, DecidableEq

def canonicalIBSHistamineH1InterventionBoundary : IBSHistamineH1InterventionBoundary := {
  randomizedH1InterventionEvidenceAcquired := true
  openLabelDoseEvidenceAcquired := true
  designsCollapsed := false
  allIBSHistamineDrivenClaimed := false
  quailEfficacyPaidByTheseTrials := false
}

end Dashi.Biology.IBSHistamineH1InterventionUpdateExact
