import Mathlib.Tactic
import NSBControl.Rational345BPHelicalBounds

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
open Rational345BPHelicalBounds

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
-- Real curl spectral laws for the genuine sqrt mode norm.
------------------------------------------------------------------------

theorem normSq_nonneg_real (k : Mode) : 0 ≤ normSq k := by
  unfold normSq
  positivity

theorem modeNorm_sq_eq_normSq (k : Mode) :
    modeNorm k ^ 2 = normSq k := by
  rw [modeNorm, Real.sq_sqrt (normSq_nonneg_real k)]

theorem modeNorm_pos_of_nonzero (k : Mode) (hk : nonzeroMode k) :
    0 < modeNorm k :=
  zero_lt_one.trans_le (modeNorm_ge_one k hk)

theorem inverseModeNorm_mul_normSq
    (k : Mode) (hk : nonzeroMode k) :
    inverseModeNorm k * normSq k = modeNorm k := by
  have hn : modeNorm k ≠ 0 := ne_of_gt (modeNorm_pos_of_nonzero k hk)
  rw [← modeNorm_sq_eq_normSq]
  field_simp [inverseModeNorm, hn]

theorem curlSymbol_add (k : Mode) (a b : Vec3) :
    curlSymbol k (a + b) = curlSymbol k a + curlSymbol k b := by
  funext j
  fin_cases j <;> simp [curlSymbol, cross, kComplex] <;> ring

theorem curlSymbol_smul (k : Mode) (c : ℂ) (v : Vec3) :
    curlSymbol k (c • v) = c • curlSymbol k v := by
  funext j
  fin_cases j <;> simp [curlSymbol, cross, kComplex] <;> ring

/-- BAC-CAB for the literal three-coordinate cross product. -/
theorem cross_k_cross_identity (k : Mode) (v : Vec3) :
    cross (kComplex k) (cross (kComplex k) v) =
      fun j =>
        (kReal k j : ℂ) * bilinearDot (kComplex k) v -
          (normSq k : ℂ) * v j := by
  funext j
  fin_cases j <;>
    simp [cross, kComplex, bilinearDot, normSq, Fin.sum_univ_succ] <;>
    ring

/-- On a transverse mode the literal curl symbol squares to |k|^2. -/
theorem curlSymbol_sq_of_transverse
    (k : Mode) (v : Vec3)
    (htrans : bilinearDot (kComplex k) v = 0) :
    curlSymbol k (curlSymbol k v) = (normSq k : ℂ) • v := by
  have hcurl :
      curlSymbol k (curlSymbol k v) =
        - cross (kComplex k) (cross (kComplex k) v) := by
    funext j
    fin_cases j <;> simp [curlSymbol, cross, kComplex] <;> ring
  rw [hcurl, cross_k_cross_identity]
  funext j
  rw [htrans]
  simp

/-- The real plus component is a genuine +|k| curl eigenvector. -/
theorem helicalPlus_curl_eigen
    (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (htrans : bilinearDot (kComplex k) (u k) = 0) :
    curlSymbol k (helicalComponent plus u k) =
      (modeNorm k : ℂ) • helicalComponent plus u k := by
  change curlSymbol k (helicalPlus k (u k)) =
    (modeNorm k : ℂ) • helicalPlus k (u k)
  have hP : leray k (u k) = u k :=
    leray_eq_self_of_transverse k (u k) hk htrans
  have hC2 : curlSymbol k (curlSymbol k (u k)) =
      (normSq k : ℂ) • u k :=
    curlSymbol_sq_of_transverse k (u k) htrans
  have hscale := inverseModeNorm_mul_normSq k hk
  funext j
  simp only [helicalPlus]
  rw [show curlSymbol k
        (fun r => ((1 : ℂ) / 2) *
          (leray k (u k) r + (inverseModeNorm k : ℂ) * curlSymbol k (u k) r)) =
      curlSymbol k
        (((1 : ℂ) / 2) •
          (leray k (u k) + (inverseModeNorm k : ℂ) • curlSymbol k (u k))) by rfl]
  rw [curlSymbol_smul, curlSymbol_add, curlSymbol_smul, hP, hC2]
  have hscaleC :
      (inverseModeNorm k : ℂ) * (normSq k : ℂ) = (modeNorm k : ℂ) := by
    exact_mod_cast hscale
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [← hscaleC]
  ring

/-- The real minus component is a genuine -|k| curl eigenvector. -/
theorem helicalMinus_curl_eigen
    (u : State) (k : Mode)
    (hk : nonzeroMode k)
    (htrans : bilinearDot (kComplex k) (u k) = 0) :
    curlSymbol k (helicalComponent minus u k) =
      (-modeNorm k : ℂ) • helicalComponent minus u k := by
  change curlSymbol k (helicalMinus k (u k)) =
    (-modeNorm k : ℂ) • helicalMinus k (u k)
  have hP : leray k (u k) = u k :=
    leray_eq_self_of_transverse k (u k) hk htrans
  have hC2 : curlSymbol k (curlSymbol k (u k)) =
      (normSq k : ℂ) • u k :=
    curlSymbol_sq_of_transverse k (u k) htrans
  have hscale := inverseModeNorm_mul_normSq k hk
  funext j
  simp only [helicalMinus]
  rw [show curlSymbol k
        (fun r => ((1 : ℂ) / 2) *
          (leray k (u k) r - (inverseModeNorm k : ℂ) * curlSymbol k (u k) r)) =
      curlSymbol k
        (((1 : ℂ) / 2) •
          (leray k (u k) - (inverseModeNorm k : ℂ) • curlSymbol k (u k))) by rfl]
  rw [curlSymbol_smul]
  have hsub :
      curlSymbol k
        (leray k (u k) - (inverseModeNorm k : ℂ) • curlSymbol k (u k)) =
      curlSymbol k (leray k (u k)) -
        curlSymbol k ((inverseModeNorm k : ℂ) • curlSymbol k (u k)) := by
    simpa [sub_eq_add_neg, curlSymbol_add, curlSymbol_smul]
  rw [hsub, curlSymbol_smul, hP, hC2]
  have hscaleC :
      (inverseModeNorm k : ℂ) * (normSq k : ℂ) = (modeNorm k : ℂ) := by
    exact_mod_cast hscale
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [← hscaleC]
  ring

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

def r823RealR571CurlEigenLawsClosed : Bool := true

def r823RealR571MultiplierDifferenceRewriteClosed : Bool := false

end Rational345R823RealHelicalCore
end NSBControl
