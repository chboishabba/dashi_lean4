import Mathlib.Tactic
import NSBControl.Rational345RealRadius4

/-!
# Real R571/R572 helical component core for the R823 decision lane

Agda R571 is field-generic: an arbitrary transverse Fourier coefficient splits
into its plus/minus helical projections, and the symmetric ordered interaction
then expands into the four sign pairs.  This file ports exactly that algebra to
the genuine real/sqrt radius-four carrier used by R830.

No R823 reserve identity, shell mask, estimate, or snapshot specialization is
asserted here.
-/

namespace NSBControl
namespace Rational345R823RealHelicalCore

open Rational345RealRadius4

inductive HelicitySign where
  | plus
  | minus
deriving DecidableEq, Repr

open HelicitySign

def signedEigenvalue : HelicitySign → Mode → ℝ
  | plus, k => modeNorm k
  | minus, k => - modeNorm k

def helicalComponent (sign : HelicitySign) (u : State) (k : Mode) : Vec3 :=
  match sign with
  | plus => helicalPlus k (u k)
  | minus => helicalMinus k (u k)

/-- Plus and minus projectors sum to the Leray projection by definition. -/
theorem helicalPlus_add_minus_eq_leray (k : Mode) (v : Vec3) :
    helicalPlus k v + helicalMinus k v = leray k v := by
  funext j
  simp [helicalPlus, helicalMinus]
  ring

/-- Leray projection fixes a nonzero transverse vector. -/
theorem leray_eq_self_of_transverse
    (k : Mode) (v : Vec3)
    (hk : nonzeroMode k)
    (htrans : bilinearDot (kComplex k) v = 0) :
    leray k v = v := by
  funext j
  simp only [leray]
  rw [if_neg hk]
  rw [htrans]
  simp

/-- Exact real helical decomposition on one physical nonzero mode. -/
theorem helical_decomposition_of_transverse
    (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (htrans : bilinearDot (kComplex k) (u k) = 0) :
    helicalComponent plus u k + helicalComponent minus u k = u k := by
  change helicalPlus k (u k) + helicalMinus k (u k) = u k
  rw [helicalPlus_add_minus_eq_leray]
  exact leray_eq_self_of_transverse k (u k) hk htrans

------------------------------------------------------------------------
-- Literal ordered/symmetric pair interaction, matching the R571 carrier.
------------------------------------------------------------------------

def orderedPairVector (k p q : Mode) (a b : Vec3) : Vec3 :=
  if Resonates p q k then
    fun j =>
      -Complex.I *
        leray k (fun r => bilinearDot a (kComplex q) * b r) j
  else 0

def pairInteractionVector (k p q : Mode) (a b : Vec3) : Vec3 :=
  orderedPairVector k p q a b + orderedPairVector k q p b a

def pairedInteraction (u : State) (p q k : Mode) : Vec3 :=
  pairInteractionVector k p q (u p) (u q)

@[simp] theorem orderedPairVector_add_left
    (k p q : Mode) (a b c : Vec3) :
    orderedPairVector k p q (a + b) c =
      orderedPairVector k p q a c + orderedPairVector k p q b c := by
  funext j
  unfold orderedPairVector
  by_cases h : Resonates p q k
  · simp [h, leray, bilinearDot]
    split_ifs <;> simp
    ring
  · simp [h]

@[simp] theorem orderedPairVector_add_right
    (k p q : Mode) (a b c : Vec3) :
    orderedPairVector k p q a (b + c) =
      orderedPairVector k p q a b + orderedPairVector k p q a c := by
  funext j
  unfold orderedPairVector
  by_cases h : Resonates p q k
  · simp [h, leray, bilinearDot]
    split_ifs <;> simp
    ring
  · simp [h]

@[simp] theorem pairInteractionVector_add_left
    (k p q : Mode) (a b c : Vec3) :
    pairInteractionVector k p q (a + b) c =
      pairInteractionVector k p q a c + pairInteractionVector k p q b c := by
  unfold pairInteractionVector
  rw [orderedPairVector_add_left, orderedPairVector_add_right]
  abel

@[simp] theorem pairInteractionVector_add_right
    (k p q : Mode) (a b c : Vec3) :
    pairInteractionVector k p q a (b + c) =
      pairInteractionVector k p q a b + pairInteractionVector k p q a c := by
  unfold pairInteractionVector
  rw [orderedPairVector_add_right, orderedPairVector_add_left]
  abel

/-- The four actual helical component interactions before the R106
multiplier-difference rewrite. -/
def fourComponentPairInteraction (u : State) (p q k : Mode) : Vec3 :=
  pairInteractionVector k p q
      (helicalComponent plus u p) (helicalComponent plus u q) +
    pairInteractionVector k p q
      (helicalComponent plus u p) (helicalComponent minus u q) +
    pairInteractionVector k p q
      (helicalComponent minus u p) (helicalComponent plus u q) +
    pairInteractionVector k p q
      (helicalComponent minus u p) (helicalComponent minus u q)

/-- Real counterpart of the first half of Agda R571: an arbitrary physical
transverse pair expands exactly into the four helical sign pairs. -/
theorem pairedInteraction_expands_four_components
    (u : State) (p q k : Mode)
    (_hres : Resonates p q k)
    (hp : nonzeroMode p) (hq : nonzeroMode q)
    (hpt : bilinearDot (kComplex p) (u p) = 0)
    (hqt : bilinearDot (kComplex q) (u q) = 0) :
    pairedInteraction u p q k = fourComponentPairInteraction u p q k := by
  have hpdec := helical_decomposition_of_transverse u p hp hpt
  have hqdec := helical_decomposition_of_transverse u q hq hqt
  unfold pairedInteraction fourComponentPairInteraction
  rw [← hpdec, ← hqdec]
  rw [pairInteractionVector_add_left]
  rw [pairInteractionVector_add_right, pairInteractionVector_add_right]
  abel

------------------------------------------------------------------------
-- R106 target syntax.  The next max-cut proves each component interaction is
-- this multiplier-difference vector on a nonzero resonant output.
------------------------------------------------------------------------

def multiplierDifferenceVector
    (signP signQ : HelicitySign)
    (u : State) (p q k : Mode) : Vec3 :=
  let λp : ℂ := signedEigenvalue signP p
  let λq : ℂ := signedEigenvalue signQ q
  (λq - λp) •
    leray k (cross (helicalComponent signP u p) (helicalComponent signQ u q))

def fourSignInner (u : State) (p q k : Mode) : Vec3 :=
  multiplierDifferenceVector plus plus u p q k +
    multiplierDifferenceVector plus minus u p q k +
    multiplierDifferenceVector minus plus u p q k +
    multiplierDifferenceVector minus minus u p q k

/-- The real irrational-helicity core is now explicit; the R106 rewrite is the
next semantic theorem rather than an assumed field adapter. -/
def r823RealR571FourComponentExpansionClosed : Bool := true

def r823RealR571MultiplierDifferenceRewriteClosed : Bool := false

end Rational345R823RealHelicalCore
end NSBControl
