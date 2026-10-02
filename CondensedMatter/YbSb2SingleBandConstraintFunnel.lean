import Mathlib

namespace CondensedMatter

/--
Reusable logical core for excluding single-band superconducting candidates
when strong-SOC candidates cannot break TRS and weak-SOC TRSB candidates are
necessarily nodal.

The physical premises are deliberately parameters.  The theorem itself is
pure logic and can be instantiated by any material-specific source package.
-/
structure SingleBandTRSBFullGapFunnel where
  Candidate : Type
  StrongSOC : Candidate → Prop
  WeakSOC : Candidate → Prop
  BreaksTRS : Candidate → Prop
  HasPointNodes : Candidate → Prop
  FullyGapped : Candidate → Prop

  socExhaustive :
    ∀ c, StrongSOC c ∨ WeakSOC c

  strongSOCNoTRSB :
    ∀ c, StrongSOC c → ¬ BreaksTRS c

  weakSOCTRSBHasPointNodes :
    ∀ c, WeakSOC c → BreaksTRS c → HasPointNodes c

  fullGapExcludesPointNodes :
    ∀ c, FullyGapped c → ¬ HasPointNodes c

namespace SingleBandTRSBFullGapFunnel

variable (F : SingleBandTRSBFullGapFunnel)

theorem no_candidate_is_both_TRSB_and_fully_gapped :
    ¬ ∃ c : F.Candidate, F.BreaksTRS c ∧ F.FullyGapped c := by
  rintro ⟨c, hTRSB, hgap⟩
  rcases F.socExhaustive c with hstrong | hweak
  · exact F.strongSOCNoTRSB c hstrong hTRSB
  · exact F.fullGapExcludesPointNodes c hgap
      (F.weakSOCTRSBHasPointNodes c hweak hTRSB)

end SingleBandTRSBFullGapFunnel

namespace YbSb2

/--
Source-facing YbSb2 package corresponding to the symmetry argument in
Kataria et al. (PRL accepted 3 Aug 2026, DOI 10.1103/drzq-lfn5):

* D2h admits only one-dimensional irreps, excluding the ordinary
  symmetry-allowed strong-SOC single-band TRSB route;
* weak-SOC single-band TRSB states have point nodes;
* experiment supports a fully gapped superconducting state.

This record does not manufacture those physical/source premises.
-/
structure SingleBandSourcePackage where
  Candidate : Type
  StrongSOC : Candidate → Prop
  WeakSOC : Candidate → Prop
  BreaksTRS : Candidate → Prop
  HasPointNodes : Candidate → Prop
  FullyGapped : Candidate → Prop

  socExhaustive :
    ∀ c, StrongSOC c ∨ WeakSOC c

  d2hStrongSOCNoTRSB :
    ∀ c, StrongSOC c → ¬ BreaksTRS c

  weakSOCTRSBPointNodes :
    ∀ c, WeakSOC c → BreaksTRS c → HasPointNodes c

  observedFullGapExcludesPointNodes :
    ∀ c, FullyGapped c → ¬ HasPointNodes c

def SingleBandSourcePackage.toFunnel
    (S : SingleBandSourcePackage) :
    SingleBandTRSBFullGapFunnel where
  Candidate := S.Candidate
  StrongSOC := S.StrongSOC
  WeakSOC := S.WeakSOC
  BreaksTRS := S.BreaksTRS
  HasPointNodes := S.HasPointNodes
  FullyGapped := S.FullyGapped
  socExhaustive := S.socExhaustive
  strongSOCNoTRSB := S.d2hStrongSOCNoTRSB
  weakSOCTRSBHasPointNodes := S.weakSOCTRSBPointNodes
  fullGapExcludesPointNodes := S.observedFullGapExcludesPointNodes

theorem no_single_band_candidate_matches_TRSB_full_gap
    (S : SingleBandSourcePackage) :
    ¬ ∃ c : S.Candidate, S.BreaksTRS c ∧ S.FullyGapped c :=
  S.toFunnel.no_candidate_is_both_TRSB_and_fully_gapped

/--
The single-band no-go theorem is intentionally typed only over the single-band
candidate carrier.  A multi-orbital INT candidate is therefore not excluded
merely by applying this theorem; a separate physical identification is needed.
-/
structure MultiOrbitalINTCandidate where
  breaksTRS : Prop
  fullyGapped : Prop
  orbitalAntisymmetric : Prop

end YbSb2
end CondensedMatter
