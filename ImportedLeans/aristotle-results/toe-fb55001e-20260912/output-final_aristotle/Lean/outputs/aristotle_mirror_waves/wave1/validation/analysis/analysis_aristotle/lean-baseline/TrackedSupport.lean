import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.DASHIValuation
import AgdaMirror.Vec15Descriptive
import AgdaMirror.ArithmeticIntegerEmbedding

/-!
# Lean mirror of `DASHI/Arithmetic/TrackedSupport.agda` (genuine, fully proved)

The tracked-support proxy: a local contribution is bounded by its output
valuation depth (`deltaAt ≤ supportAt`), and the global support score is the
corresponding 15-lane gamma sum.  Includes the componentwise monotonicity of
the 15-lane sum (`sum15≤`) and the global bound
`totalPressure ≤ trackedSupport`.
-/

namespace AgdaMirror.TrackedSupport

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Descriptive
open AgdaMirror.ArithmeticIntegerEmbedding
open SSP

/-- Local support proxy = the output valuation depth `gammaAt`. -/
def supportAt (p : SSP) (x y : IntCarrier) : Nat := gammaAt p x y

/-- 15-lane support vector. -/
def support15 (x y : IntCarrier) : Vec15 Nat := gamma15 x y

/-- Global tracked support = the gamma sum. -/
def trackedSupport (x y : IntCarrier) : Nat := gammaSum x y

/-- Componentwise monotonicity of the 15-lane sum (Agda `sum15≤`). -/
theorem sum15_le {u v : Vec15 Nat}
    (h2 : u.e2 ≤ v.e2) (h3 : u.e3 ≤ v.e3) (h5 : u.e5 ≤ v.e5) (h7 : u.e7 ≤ v.e7)
    (h11 : u.e11 ≤ v.e11) (h13 : u.e13 ≤ v.e13) (h17 : u.e17 ≤ v.e17)
    (h19 : u.e19 ≤ v.e19) (h23 : u.e23 ≤ v.e23) (h29 : u.e29 ≤ v.e29)
    (h31 : u.e31 ≤ v.e31) (h41 : u.e41 ≤ v.e41) (h47 : u.e47 ≤ v.e47)
    (h59 : u.e59 ≤ v.e59) (h71 : u.e71 ≤ v.e71) :
    sum u ≤ sum v :=
  sum_mono h2 h3 h5 h7 h11 h13 h17 h19 h23 h29 h31 h41 h47 h59 h71

/-- Local bound: the local cancellation lift is bounded by the output depth. -/
theorem deltaAt_le_supportAt (p : SSP) (x y : IntCarrier) :
    deltaAt p x y ≤ supportAt p x y := by
  unfold supportAt deltaAt
  exact Nat.sub_le _ _

/-- Global tracked bound: total pressure is bounded by tracked support. -/
theorem totalPressure_le_trackedSupport (x y : IntCarrier) :
    totalPressure x y ≤ trackedSupport x y := by
  unfold totalPressure trackedSupport gammaSum delta15 gamma15 mapPrimes15 sum
  simp only
  have h := fun p => deltaAt_le_supportAt p x y
  simp only [supportAt] at h
  have := h p2; have := h p3; have := h p5; have := h p7; have := h p11
  have := h p13; have := h p17; have := h p19; have := h p23; have := h p29
  have := h p31; have := h p41; have := h p47; have := h p59; have := h p71
  omega

end AgdaMirror.TrackedSupport
