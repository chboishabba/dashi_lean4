/-
# `NSUnforced` — the unforced DASHI Navier–Stokes A-programme, in Lean

Aggregate for the modules of the unforced A lane.  Nothing here touches the
published forced-breakdown C/D results, and nothing here imports Yang–Mills
material.

* `NSUnforced.SignedFullSquare` — the R543/R566/R567 full ordered square over
  `ℝ`, and the **exact** signed Gram collapse of the commutator-only pair
  scalar (all cancellation performed before any positive majorisation).
* `NSUnforced.HelicalMultiplierDifference` — the literal R571 signed `±y`
  multiplier-difference carrier: the homochiral output gain
  `|λ_q^s − λ_p^s| ≤ ‖k‖`, the exact homochiral signed cancellation, and the
  *decisive typed obstruction* showing the heterochiral channel admits no such
  gain.
* `NSUnforced.ChannelSchur` — the Schur test reducing both channel-square
  receipts of the frontier to row/column bounds on the Gram weight matrix.
* `NSUnforced.CutoffUniformBudget` — the absorption/Grönwall engine producing a
  cutoff-independent spacetime budget from a pointwise absorption receipt.
* `NSUnforced.A1Budget568` — `CommutatorOnlySpacetimeBudget568` over `ℝ` and its
  reduction, including the post-collapse Young/Schur step.
* `NSUnforced.A2CriticalCeiling` — the independent A2 critical-production
  ceiling, built on the preserved donor Waleffe Kato/Duhamel payment.
* `NSUnforced.DualConsumer414` — the R414 dual consumer, plus the two
  non-collapse theorems showing neither payment can discharge the other.
* `NSUnforced.Frontier` — the residual A1 obligation as a single named
  proposition, with a proof that it suffices.
-/
import NSUnforced.SignedFullSquare
import NSUnforced.ChannelSchur
import NSUnforced.HelicalMultiplierDifference
import NSUnforced.CutoffUniformBudget
import NSUnforced.A1Budget568
import NSUnforced.A2CriticalCeiling
import NSUnforced.DualConsumer414
import NSUnforced.Frontier
