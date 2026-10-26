import Dashi.Biology.QuailEggHistamineGutSnowballExact

namespace Dashi.Biology.QuailEggHistamineGutParetoSnowballExact

open Dashi.Biology.GABAPhenotypeEvidenceExact
open Dashi.Biology.QuailEggHistamineGutSnowballExact

def yang2020PHSource : AttributedSource :=
  mkDOISource
    "Qin Yang; Ju Meng; Wei Zhang; Lu Liu; Laping He; Li Deng; Xuefeng Zeng; Chun Ye"
    "Effects of Amino Acid Decarboxylase Genes and pH on the Amine Formation of Enteric Bacteria From Chinese Traditional Fermented Fish (Suan Yu)"
    "Frontiers in Microbiology 11:1130" "2020"
    "10.3389/fmicb.2020.01130" "https://doi.org/10.3389/fmicb.2020.01130"
    "Pays strain- and medium-specific pH effects on microbial histamine/biogenic-amine production; not a human-gut pH law."

structure PHHistamineReceipt where
  source : AttributedSource
  pHDependenceObserved : Bool
  strainSpecificityRetained : Bool
  humanGutTransferPaid : Bool
  boundary : String
  deriving Repr, DecidableEq

def microbialPHHistamineReceipt : PHHistamineReceipt := {
  source := yang2020PHSource
  pHDependenceObserved := true
  strainSpecificityRetained := true
  humanGutTransferPaid := false
  boundary := "Gut transfer requires local pH, substrate, strain abundance/expression and in-vivo histamine flux; fermented-food culture optima are not transplanted directly."
}

inductive GutAcquisitionStatus where
  | paidBounded | experimentRequired | transportOrExposureRequired | replicationRequired
  deriving Repr, DecidableEq

structure GutAcquisitionNode where
  label : String
  status : GutAcquisitionStatus
  paidReference : String
  residual : String
  deriving Repr, DecidableEq

def quailAlbumenNode : GutAcquisitionNode := {
  label := "quail egg albumen mast-cell degranulation"
  status := .paidBounded
  paidReference := "Lianto 2018 mouse PCA + HMC-1 anti-degranulation evidence"
  residual := "human digestion/exposure, dose-response, IBS phenotype, safety/allergenicity and replicated clinical endpoint"
}

def ovomucoidNode : GutAcquisitionNode := {
  label := "quail ovomucoid molecular/cell mechanism"
  status := .paidBounded
  paidReference := "Hao 2023 recombinant ovomucoid trypsin/degranulation evidence"
  residual := "same-object bridge from recombinant protein to digested food exposure and human intestinal target engagement"
}

def ibsHistamineMechanismNode : GutAcquisitionNode := {
  label := "IBS histamine neuroimmune mechanism"
  status := .paidBounded
  paidReference := "De Palma 2022 microbial histamine/H4 plus Wouters 2016 H1/TRPV1 human evidence"
  residual := "phenotype stratification and source attribution across microbial, mast-cell, dietary and clearance terms"
}

def gutDAOCompartmentNode : GutAcquisitionNode := {
  label := "intestinal DAO versus serum/central histamine compartments"
  status := .transportOrExposureRequired
  paidReference := "Agda HistamineCompartmentClearanceExact plus Schnedl 2021 serum-DAO != gut-DAO boundary"
  residual := "paired/local intestinal DAO activity with luminal/mucosal histamine, timing, diet, microbiome and symptom endpoints"
}

def microbialPHNode : GutAcquisitionNode := {
  label := "microbial histamine pH dependence"
  status := .paidBounded
  paidReference := "Yang 2020 pH- and strain-dependent histamine production in cultured enteric bacteria"
  residual := "gut-relevant local pH + substrate + hdc expression + strain-resolved histamine flux in vivo"
}

def quailIBSTrialNode : GutAcquisitionNode := {
  label := "quail egg / ovomucoid IBS intervention"
  status := .experimentRequired
  paidReference := "preclinical anti-degranulation evidence and independent human IBS histamine-mechanism evidence coexist but are not intervention-welded"
  residual := "controlled human IBS exposure/comparator, symptom/visceral endpoint, mast-cell/histamine/DAO assays and allergy/tolerability surveillance"
}

def canonicalGutAcquisitionFrontier : List GutAcquisitionNode := [
  quailAlbumenNode, ovomucoidNode, ibsHistamineMechanismNode,
  gutDAOCompartmentNode, microbialPHNode, quailIBSTrialNode
]

structure QuailEggHistamineParetoBoundary where
  preclinicalDoesNotCreateClinicalEfficacy : Bool
  pHStudyDoesNotCreateGutPHLaw : Bool
  compartmentAndSourceTermsRemainSeparate : Bool
  nextPromotionRequiresNewData : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggHistamineParetoBoundary : QuailEggHistamineParetoBoundary := {
  preclinicalDoesNotCreateClinicalEfficacy := true
  pHStudyDoesNotCreateGutPHLaw := true
  compartmentAndSourceTermsRemainSeparate := true
  nextPromotionRequiresNewData := true
}

end Dashi.Biology.QuailEggHistamineGutParetoSnowballExact
