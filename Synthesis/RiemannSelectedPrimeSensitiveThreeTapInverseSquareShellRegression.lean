import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAsymptoticBalance

/-!
# Regression: literal inverse-square shell compiler

The numerical dyadic series and its conversion to the normalized log-over-t
Route-A tail are paid.  The genuinely open theorem is the carrier partition:
the exact complementary zero tsum must still be dominated by the dyadic shell
majorant on the literal all-real `Ncount` carrier.

This regression therefore checks the paid implication rather than naming a
nonexistent unconditional producer.  When a source theorem eventually proves
`∃ Ashell, ThreeTapInverseSquareShellPartitionBound Ashell`, it plugs directly
into `exists_threeTapInverseSquareTailBound_of_shellPartition`.
-/

noncomputable section
namespace Synthesis

example
    (h : ∃ Ashell : ℝ, ThreeTapInverseSquareShellPartitionBound Ashell) :
    ∃ Ctail : ℝ, ThreeTapInverseSquareTailBound Ctail :=
  exists_threeTapInverseSquareTailBound_of_shellPartition h

example {Ashell : ℝ}
    (h : ThreeTapInverseSquareShellPartitionBound Ashell) :
    ThreeTapInverseSquareTailBound (4 * Ashell) :=
  h.toTailBound

end Synthesis
