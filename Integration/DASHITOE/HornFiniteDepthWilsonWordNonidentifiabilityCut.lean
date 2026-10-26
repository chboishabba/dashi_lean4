import Mathlib

/-!
# Finite Wilson-word indistinguishability: wild Hatcher stage vs tame rose

Original mathematical roots:
* Hatcher, Algebraic Topology Example 2B.2, pp171-172:
  stage G_n = FreeGroup (Fin (3*2^n)) for three factor sectors,
  assuming the ACTUAL #1244 three-sector geometric source map.
* Hatcher Example 1.21: wedge of r circles has free group F_r.
  Upstream Deicyde/hatcher-at already formalises
  Hatcher.fundamentalGroupEquivWedgeCircles; that construction
  must be REUSED, not represented as new DASHI topology.
* Original C3 three-copy wild geometry and free products: #1244;
  original selected SU3 W: Agda neutrino #1247;
  spectral and regularity consumers: Agda #1249 / Lean #84.

DERIVED NO-GO for a FINITE SOURCE STAGE:
For any group G and any source stage equivalence
G ≃* FreeGroup (Fin (3*2^n)), EVERY group homomorphism
G -> SU3, its word values and any class-function
observations can be reproduced on the tame rose's
free group by precomposition with the inverse equivalence.
This applies to every word at that stage, not merely a
finite list of individually chosen loops. A C3-compatible
sector permutation is also algebraically reproduced by
relabeling the rose generators (actual spatial symmetry
does NOT follow). This does not prove equivalence of
the full infinite spaces, Euclidean lengths, regularity,
physical experiment, or a wild-specific observable.

This source is NOT Lean-kernel checked; no local Lake executable.
-/

namespace DASHIHornFiniteWilsonNonidentifiability

universe u v w

variable {Source : Type u} {Receiver : Type v}
  [Group Source] [Group Receiver]

/-- Only the FINITE stage is isomorphic to a tame rose free
group. The same object is NOT the entire wild group colimit. -/
def tameRoseReceiver (n : ℕ)
    (stageToRose : Source ≃* FreeGroup (Fin (3 * 2^n)))
    (sourceHolonomy : Source →* Receiver) :
    FreeGroup (Fin (3 * 2^n)) →* Receiver :=
  sourceHolonomy.comp stageToRose.symm.toMonoidHom

theorem everyFiniteStageWordMatches (n : ℕ)
    (stageToRose : Source ≃* FreeGroup (Fin (3 * 2^n)))
    (sourceHolonomy : Source →* Receiver)
    (word : Source) :
    tameRoseReceiver n stageToRose sourceHolonomy
      (stageToRose word) = sourceHolonomy word := by
  change sourceHolonomy (stageToRose.symm (stageToRose word)) =
    sourceHolonomy word
  simp

/-- Any observable of that actual receiver element, including
characteristic polynomial / Wilson trace / class function,
matches automatically. No gauge-invariant experimental
wildness discriminator can be extracted from stage WORDS alone. -/
theorem anyFiniteWilsonObservableMatches
    {Observed : Type w} (n : ℕ)
    (stageToRose : Source ≃* FreeGroup (Fin (3 * 2^n)))
    (sourceHolonomy : Source →* Receiver)
    (observed : Receiver → Observed) (word : Source) :
    observed
      (tameRoseReceiver n stageToRose sourceHolonomy
        (stageToRose word)) =
      observed (sourceHolonomy word) := by
  rw [everyFiniteStageWordMatches]

/-- Simultaneous finite queries still do not discriminate the
two marked-stage models. The source-map equivalence is an
EXPLICIT premise, not Hatcher infinite wild-geometry proof. -/
theorem allFiniteWilsonQueriesMatch
    {Observed : Type w} (n : ℕ)
    (stageToRose : Source ≃* FreeGroup (Fin (3 * 2^n)))
    (sourceHolonomy : Source →* Receiver)
    (observed : Receiver → Observed) (words : List Source) :
    words.map (fun x =>
      observed
        (tameRoseReceiver n stageToRose sourceHolonomy
          (stageToRose x))) =
    words.map (fun x => observed (sourceHolonomy x)) := by
  apply List.map_congr_left
  intro x hx
  exact anyFiniteWilsonObservableMatches
    n stageToRose sourceHolonomy observed x

end DASHIHornFiniteWilsonNonidentifiability
