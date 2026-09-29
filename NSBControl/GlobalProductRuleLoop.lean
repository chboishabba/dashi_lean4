import Mathlib

namespace NSBControl
namespace GlobalProductRuleLoop

/-- Load-bearing scalar mirror of Agda R773-R774. -/
theorem global_product_rule_loop
    (base dyadic residual combined production : ℝ)
    (hProductRule : 9 * base - 2 * dyadic = 2 * residual)
    (hResidual : residual = 3 * (combined - production)) :
    9 * base - 2 * dyadic = 6 * (combined - production) := by
  rw [hProductRule, hResidual]
  ring

inductive Regime where
  | lowHigh
  | highLow
  | highHigh
  | comparable
  deriving DecidableEq, Repr

def swapRegime : Regime → Regime
  | .lowHigh => .highLow
  | .highLow => .lowHigh
  | .highHigh => .highHigh
  | .comparable => .comparable

theorem swapRegime_involutive (r : Regime) :
    swapRegime (swapRegime r) = r := by
  cases r <;> rfl

structure OrbitProfile where
  base : Regime
  pLeg : Regime
  qLeg : Regime
  deriving DecidableEq, Repr

def swapProfile (p : OrbitProfile) : OrbitProfile :=
  ⟨swapRegime p.base, p.qLeg, p.pLeg⟩

theorem swapProfile_involutive (p : OrbitProfile) :
    swapProfile (swapProfile p) = p := by
  cases p
  simp [swapProfile, swapRegime_involutive]

/--
Abstract mirror of the R775 swap law.  The physical Agda theorem supplies the
three equalities from R119/R129; Lean checks the record transport only.
-/
theorem orbitProfile_swap
    (profile profileSwap : OrbitProfile)
    (hBase : profileSwap.base = swapRegime profile.base)
    (hP : profileSwap.pLeg = profile.qLeg)
    (hQ : profileSwap.qLeg = profile.pLeg) :
    profileSwap = swapProfile profile := by
  cases profile
  cases profileSwap
  simp_all [swapProfile]

end GlobalProductRuleLoop
end NSBControl
