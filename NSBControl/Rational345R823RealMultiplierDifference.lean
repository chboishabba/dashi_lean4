import Mathlib.Tactic
import NSBControl.Rational345R823RealHelicalCore

/-!
# Real R106 multiplier-difference rewrite

This is the decisive second half of the real R571 port.  The symmetric ordered
Navier--Stokes interaction is first rewritten as the Leray projection of the
curl-slot difference

  a × curl_q b - curl_p a × b.

For helical components, the real curl-eigen laws from
`Rational345R823RealHelicalCore` then turn this into

  (lambda_q - lambda_p) P_k (a × b).

All mode norms are the genuine real square roots used by the evolving R830
trajectory.
-/

namespace NSBControl
namespace Rational345R823RealHelicalCore

open Rational345RealRadius4

@[simp] theorem cross_smul_left (c : ℂ) (a b : Vec3) :
    cross (c • a) b = c • cross a b := by
  funext j
  fin_cases j <;> simp [cross] <;> ring

@[simp] theorem cross_smul_right (c : ℂ) (a b : Vec3) :
    cross a (c • b) = c • cross a b := by
  funext j
  fin_cases j <;> simp [cross] <;> ring

@[simp] theorem leray_smul (k : Mode) (c : ℂ) (v : Vec3) :
    leray k (c • v) = c • leray k v := by
  funext j
  unfold leray
  by_cases hz : isZeroMode k
  · simp [hz]
  · simp [hz, bilinearDot]
    ring

theorem resonates_swap {p q k : Mode} (h : Resonates p q k) :
    Resonates q p k := by
  intro j
  have hj := h j
  omega

theorem kReal_add_of_resonates
    {p q k : Mode} (h : Resonates p q k) (j : Fin 3) :
    kReal p j + kReal q j = kReal k j := by
  simpa [kReal] using
    congrArg (fun z : ℤ => (z : ℝ)) (h j)

/-- Fourier convective/rotational identity on the literal finite carrier.
No helicity premise is used here. -/
theorem pairInteractionVector_eq_projectedCurlDifference
    (k p q : Mode) (a b : Vec3)
    (hres : Resonates p q k)
    (hk : nonzeroMode k) :
    pairInteractionVector k p q a b =
      leray k
        (cross a (curlSymbol q b) - cross (curlSymbol p a) b) := by
  have hswap : Resonates q p k := resonates_swap hres
  have h0 := kReal_add_of_resonates hres (0 : Fin 3)
  have h1 := kReal_add_of_resonates hres (1 : Fin 3)
  have h2 := kReal_add_of_resonates hres (2 : Fin 3)
  funext j
  fin_cases j <;>
    simp [pairInteractionVector, orderedPairVector, hres, hswap,
      leray, hk, curlSymbol, cross, bilinearDot, kComplex,
      normSq, Fin.sum_univ_succ] <;>
    rw [← h0, ← h1, ← h2] <;>
    ring

/-- One real helical sign-pair is exactly the R106 multiplier-difference
vector. -/
theorem componentPair_is_multiplierDifference
    (u : State) (p q k : Mode)
    (signP signQ : HelicitySign)
    (hres : Resonates p q k)
    (hk : nonzeroMode k)
    (hp : nonzeroMode p) (hq : nonzeroMode q)
    (hpt : bilinearDot (kComplex p) (u p) = 0)
    (hqt : bilinearDot (kComplex q) (u q) = 0) :
    pairInteractionVector k p q
        (helicalComponent signP u p) (helicalComponent signQ u q) =
      multiplierDifferenceVector signP signQ u p q k := by
  let a := helicalComponent signP u p
  let b := helicalComponent signQ u q
  let λp : ℂ := signedEigenvalue signP p
  let λq : ℂ := signedEigenvalue signQ q

  have hpEig : curlSymbol p a = λp • a := by
    cases signP with
    | plus =>
        exact helicalPlus_curl_eigen u p hp hpt
    | minus =>
        simpa [a, λp, signedEigenvalue] using
          helicalMinus_curl_eigen u p hp hpt

  have hqEig : curlSymbol q b = λq • b := by
    cases signQ with
    | plus =>
        exact helicalPlus_curl_eigen u q hq hqt
    | minus =>
        simpa [b, λq, signedEigenvalue] using
          helicalMinus_curl_eigen u q hq hqt

  rw [pairInteractionVector_eq_projectedCurlDifference k p q a b hres hk]
  rw [hqEig, hpEig, cross_smul_right, cross_smul_left]
  have hslot : λq • cross a b - λp • cross a b =
      (λq - λp) • cross a b := by
    exact (sub_smul λq λp (cross a b)).symm
  rw [hslot, leray_smul]
  rfl

/-- All four sign-pair rewrites combine to the literal R572 four-sign inner
vector. -/
theorem fourComponentPairInteraction_eq_fourSignInner
    (u : State) (p q k : Mode)
    (hres : Resonates p q k)
    (hk : nonzeroMode k)
    (hp : nonzeroMode p) (hq : nonzeroMode q)
    (hpt : bilinearDot (kComplex p) (u p) = 0)
    (hqt : bilinearDot (kComplex q) (u q) = 0) :
    fourComponentPairInteraction u p q k = fourSignInner u p q k := by
  unfold fourComponentPairInteraction fourSignInner
  rw [componentPair_is_multiplierDifference u p q k plus plus hres hk hp hq hpt hqt]
  rw [componentPair_is_multiplierDifference u p q k plus minus hres hk hp hq hpt hqt]
  rw [componentPair_is_multiplierDifference u p q k minus plus hres hk hp hq hpt hqt]
  rw [componentPair_is_multiplierDifference u p q k minus minus hres hk hp hq hpt hqt]

/-- Real R571 is closed on the same physical carrier used by R830. -/
def r823RealR571MultiplierDifferenceRewriteClosed : Bool := true

end Rational345R823RealHelicalCore
end NSBControl
