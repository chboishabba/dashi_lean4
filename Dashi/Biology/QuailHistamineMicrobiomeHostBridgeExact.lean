import Dashi.Biology.QuailEggHistamineGutSnowballExact

namespace Dashi.Biology.QuailHistamineMicrobiomeHostBridgeExact

open Dashi.Biology.QuailEggHistamineGutSnowballExact

structure MicrobiomeHostRoute where
  microbialMetaboliteRoute : Bool
  immuneRoute : Bool
  vagalOrNeuralRoute : Bool
  appetiteOwnershipInferred : Bool
  deriving Repr, DecidableEq

structure QuailHistamineMicrobiomeHostBridge where
  microbialHistamineEvidence : IBSMicrobialHistamineReceipt
  agdaHostOwnerReference : String
  histamineRoute : MicrobiomeHostRoute
  deriving Repr, DecidableEq

def canonicalQuailHistamineMicrobiomeHostBridge : QuailHistamineMicrobiomeHostBridge := {
  microbialHistamineEvidence := dePalma2022IBSHistamineReceipt
  agdaHostOwnerReference := "DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary.canonicalMicrobiomeHostAppetiteBoundary"
  histamineRoute := {
    microbialMetaboliteRoute := true
    immuneRoute := true
    vagalOrNeuralRoute := false
    appetiteOwnershipInferred := false
  }
}

structure QuailHistamineMicrobiomeHostBoundary where
  microbiomeInfluenceRetained : Bool
  microbialHistamineIsOneRouteNotWholeHostState : Bool
  immuneAndMetaboliteRoutesCanBeWelded : Bool
  neuralRouteRequiresSeparateEvidence : Bool
  appetiteOrCravingClaimNotPromoted : Bool
  deriving Repr, DecidableEq

def canonicalQuailHistamineMicrobiomeHostBoundary : QuailHistamineMicrobiomeHostBoundary := {
  microbiomeInfluenceRetained := true
  microbialHistamineIsOneRouteNotWholeHostState := true
  immuneAndMetaboliteRoutesCanBeWelded := true
  neuralRouteRequiresSeparateEvidence := true
  appetiteOrCravingClaimNotPromoted := true
}

end Dashi.Biology.QuailHistamineMicrobiomeHostBridgeExact
