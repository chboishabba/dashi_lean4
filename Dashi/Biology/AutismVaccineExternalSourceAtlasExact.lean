namespace Dashi.Biology.AutismVaccineExternalSourceAtlasExact

structure AttributedSourceReceipt where
  key : String
  authorsOrOwner : String
  title : String
  venue : String
  year : String
  doi : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def oct2026TranscriptSource : AttributedSourceReceipt := {
  key := "oct-2026-transcript"
  authorsOrOwner := "unidentified speaker in user-supplied transcript"
  title := "transcript-2026-10-03.srt"
  venue := "user-supplied SRT transcript"
  year := "2026"
  doi := ""
  authorityBoundary := "Primary source for transcript claims only; speaker identity is not inferred."
}

def hbomberguyMeasuredResponseSource : AttributedSourceReceipt := {
  key := "hbomberguy-measured-response"
  authorsOrOwner := "Hbomberguy (Harry Brewis)"
  title := "Vaccines and Autism: A Measured Response"
  venue := "user-supplied transcript of published video essay"
  year := "2021"
  doi := ""
  authorityBoundary := "Primary source for Hbomberguy narration; quoted speakers retain separate ownership."
}

def hviid2019Source : AttributedSourceReceipt := {
  key := "hviid-2019"
  authorsOrOwner := "Anders Hviid; Jørgen Vinsløv Hansen; Morten Frisch; Mads Melbye"
  title := "Measles, Mumps, Rubella Vaccination and Autism: A Nationwide Cohort Study"
  venue := "Annals of Internal Medicine 170(8):513-520"
  year := "2019"
  doi := "10.7326/M18-2101"
  authorityBoundary := "Pays the nationwide Danish MMR/autism no-association result within the studied population/design."
}

def cochrane2020Source : AttributedSourceReceipt := {
  key := "cochrane-2020"
  authorsOrOwner := "Vittorio Demicheli; Alessandro Rivetti; Maria Grazia Debalini; Carlo Di Pietrantonj"
  title := "Vaccines for measles, mumps, rubella, and varicella in children"
  venue := "Cochrane Database of Systematic Reviews"
  year := "2020"
  doi := "10.1002/14651858.CD004407.pub4"
  authorityBoundary := "Pays review-level effectiveness/safety findings; scope remains review- and outcome-specific."
}

def bmjRetractionReport2010Source : AttributedSourceReceipt := {
  key := "bmj-retraction-2010"
  authorsOrOwner := "Clare Dyer"
  title := "Lancet retracts Wakefield's MMR paper"
  venue := "BMJ 340:c696"
  year := "2010"
  doi := "10.1136/bmj.c696"
  authorityBoundary := "Pays the retraction/GMC context record, not the population causal estimate."
}

def bmjFraud2011Source : AttributedSourceReceipt := {
  key := "bmj-fraud-2011"
  authorsOrOwner := "Fiona Godlee; Jane Smith; Harvey Marcovitch"
  title := "Wakefield's article linking MMR vaccine and autism was fraudulent"
  venue := "BMJ 342:c7452"
  year := "2011"
  doi := "10.1136/bmj.c7452"
  authorityBoundary := "Pays BMJ's fraud characterization; epidemiologic no-association remains separately sourced."
}

def nyhan2014Source : AttributedSourceReceipt := {
  key := "nyhan-2014"
  authorsOrOwner := "Brendan Nyhan; Jason Reifler; Sean Richey; Gary L Freed"
  title := "Effective messages in vaccine promotion: a randomized trial"
  venue := "Pediatrics 133(4):e835-e842"
  year := "2014"
  doi := "10.1542/peds.2013-2365"
  authorityBoundary := "Pays the 1,759-parent trial-specific outcomes, not a universal backfire law."
}

def swireThompson2022Source : AttributedSourceReceipt := {
  key := "swire-thompson-2022"
  authorsOrOwner := "Briony Swire-Thompson et al."
  title := "The backfire effect after correcting misinformation is strongly associated with reliability"
  venue := "Journal of Experimental Psychology: General 151(7):1655-1665"
  year := "2022"
  doi := "10.1037/xge0001131"
  authorityBoundary := "Pays evidence against a general correction-backfire effect in tested items/designs."
}

end Dashi.Biology.AutismVaccineExternalSourceAtlasExact
