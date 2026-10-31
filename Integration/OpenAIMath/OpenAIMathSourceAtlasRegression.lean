import Integration.OpenAIMath.SourceAtlas

namespace Integration.OpenAIMath.OpenAIMathSourceAtlasRegression

open Integration.OpenAIMath

example : quasiRiemann.familyId = "003" := rfl
example : quasiRiemann.authority = UpstreamAuthorityLevel.leanDeclaration := rfl
example : quasiRiemann.declaration = "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re" := rfl
example : quasiRiemann.solutionModule = "OAI.NumberTheory.DirichletL.Nonvanishing" := rfl

example : uniqueGamesMaxCut.familyId = "102" := rfl
example : relativisticVlasovMaxwell.familyId = "362" := rfl
example : forcedNavierStokesComputation.familyId = "376" := rfl

example : hodgeCM.authority = UpstreamAuthorityLevel.manuscript := rfl
example : bsdLowSelmer.authority = UpstreamAuthorityLevel.manuscript := rfl

example : quasiRiemann.provesFullRiemannHypothesis = false := rfl
example : forcedNavierStokesComputation.provesClayNavierStokes = false := rfl
example : uniqueGamesMaxCut.provesPNotEqualsNP = false := rfl
example : hodgeCM.provesGeneralHodgeConjecture = false := rfl
example : bsdLowSelmer.provesGeneralBSD = false := rfl

end Integration.OpenAIMath.OpenAIMathSourceAtlasRegression
