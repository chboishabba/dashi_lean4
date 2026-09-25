import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Omega

namespace NSBControl
namespace CyclicHelicalVectorTransform

abbrev Mode := Fin 3 → ℤ

inductive HelicitySign where
  | plus
  | minus
deriving DecidableEq, Repr

structure Triad where
  p : Mode
  q : Mode
  k : Mode
  resonance : p + q = k

def pEnergyLeg (τ : Triad) : Triad where
  p := τ.k
  q := -τ.q
  k := τ.p
  resonance := by
    funext i
    have h := congrFun τ.resonance i
    omega

def qEnergyLeg (τ : Triad) : Triad where
  p := τ.k
  q := -τ.p
  k := τ.q
  resonance := by
    funext i
    have h := congrFun τ.resonance i
    omega

@[simp] theorem pEnergyLeg_p (τ : Triad) : (pEnergyLeg τ).p = τ.k := rfl
@[simp] theorem pEnergyLeg_q (τ : Triad) : (pEnergyLeg τ).q = -τ.q := rfl
@[simp] theorem pEnergyLeg_k (τ : Triad) : (pEnergyLeg τ).k = τ.p := rfl

@[simp] theorem qEnergyLeg_p (τ : Triad) : (qEnergyLeg τ).p = τ.k := rfl
@[simp] theorem qEnergyLeg_q (τ : Triad) : (qEnergyLeg τ).q = -τ.p := rfl
@[simp] theorem qEnergyLeg_k (τ : Triad) : (qEnergyLeg τ).k = τ.q := rfl

def signedEigenvalue
    (modeNorm : Mode → ℝ) (sign : HelicitySign) (m : Mode) : ℝ :=
  match sign with
  | .plus => modeNorm m
  | .minus => -modeNorm m

theorem signedEigenvalue_neg
    (modeNorm : Mode → ℝ)
    (modeNormEven : ∀ m, modeNorm (-m) = modeNorm m)
    (sign : HelicitySign) (m : Mode) :
    signedEigenvalue modeNorm sign (-m) =
      signedEigenvalue modeNorm sign m := by
  cases sign <;> simp [signedEigenvalue, modeNormEven]

theorem plusPlusCoefficient (a b : ℝ) :
    b - a = b - a := rfl

theorem plusMinusCoefficient (a b : ℝ) :
    (-b) - a = -(a + b) := by ring

theorem minusPlusCoefficient (a b : ℝ) :
    b - (-a) = a + b := by ring

theorem minusMinusCoefficient (a b : ℝ) :
    (-b) - (-a) = a - b := by ring


def baseCoefficient
    (modeNorm : Mode → ℝ)
    (τ : Triad) (signP signQ : HelicitySign) : ℝ :=
  signedEigenvalue modeNorm signQ τ.q -
    signedEigenvalue modeNorm signP τ.p

def pLegCoefficient
    (modeNorm : Mode → ℝ)
    (τ : Triad) (signK signQ : HelicitySign) : ℝ :=
  signedEigenvalue modeNorm signQ τ.q -
    signedEigenvalue modeNorm signK τ.k

def qLegCoefficient
    (modeNorm : Mode → ℝ)
    (τ : Triad) (signK signP : HelicitySign) : ℝ :=
  signedEigenvalue modeNorm signP τ.p -
    signedEigenvalue modeNorm signK τ.k

theorem orientedCyclicCoefficient_zero
    (modeNorm : Mode → ℝ)
    (τ : Triad)
    (signP signQ signK : HelicitySign) :
    baseCoefficient modeNorm τ signP signQ -
      pLegCoefficient modeNorm τ signK signQ +
      qLegCoefficient modeNorm τ signK signP = 0 := by
  unfold baseCoefficient pLegCoefficient qLegCoefficient
  ring

section Vector

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

variable (modeNorm : Mode → ℝ)
variable (component : HelicitySign → Mode → V)
variable (project : Mode → V → V)
variable (cross : V → V → V)
variable (conjugate : V → V)

def channelVector (τ : Triad) (signP signQ : HelicitySign) : V :=
  (signedEigenvalue modeNorm signQ τ.q -
      signedEigenvalue modeNorm signP τ.p) •
    project τ.k (cross (component signP τ.p) (component signQ τ.q))

def baseChannelVector (τ : Triad) (signP signQ : HelicitySign) : V :=
  channelVector modeNorm component project cross τ signP signQ

def pLegChannelVector (τ : Triad) (signK signQ : HelicitySign) : V :=
  (signedEigenvalue modeNorm signQ τ.q -
      signedEigenvalue modeNorm signK τ.k) •
    project τ.p
      (cross
        (component signK τ.k)
        (conjugate (component signQ τ.q)))

def qLegChannelVector (τ : Triad) (signK signP : HelicitySign) : V :=
  (signedEigenvalue modeNorm signP τ.p -
      signedEigenvalue modeNorm signK τ.k) •
    project τ.q
      (cross
        (component signK τ.k)
        (conjugate (component signP τ.p)))

theorem baseChannel_meaning
    (τ : Triad) (signP signQ : HelicitySign) :
    channelVector modeNorm component project cross τ signP signQ =
      baseChannelVector modeNorm component project cross τ signP signQ := rfl

theorem pEnergyLeg_channel_meaning
    (modeNormEven : ∀ m, modeNorm (-m) = modeNorm m)
    (componentReality :
      ∀ sign m, component sign (-m) = conjugate (component sign m))
    (τ : Triad) (signK signQ : HelicitySign) :
    channelVector modeNorm component project cross
        (pEnergyLeg τ) signK signQ =
      pLegChannelVector
        modeNorm component project cross conjugate τ signK signQ := by
  simp only [channelVector, pLegChannelVector, pEnergyLeg_p, pEnergyLeg_q,
    pEnergyLeg_k]
  rw [signedEigenvalue_neg modeNorm modeNormEven signQ τ.q]
  rw [componentReality signQ τ.q]

theorem qEnergyLeg_channel_meaning
    (modeNormEven : ∀ m, modeNorm (-m) = modeNorm m)
    (componentReality :
      ∀ sign m, component sign (-m) = conjugate (component sign m))
    (τ : Triad) (signK signP : HelicitySign) :
    channelVector modeNorm component project cross
        (qEnergyLeg τ) signK signP =
      qLegChannelVector
        modeNorm component project cross conjugate τ signK signP := by
  simp only [channelVector, qLegChannelVector, qEnergyLeg_p, qEnergyLeg_q,
    qEnergyLeg_k]
  rw [signedEigenvalue_neg modeNorm modeNormEven signP τ.p]
  rw [componentReality signP τ.p]

def threeOuterLegChannel
    (τ : Triad)
    (signP signQ signK : HelicitySign) : V :=
  baseChannelVector modeNorm component project cross τ signP signQ +
  pLegChannelVector modeNorm component project cross conjugate τ signK signQ +
  qLegChannelVector modeNorm component project cross conjugate τ signK signP

theorem threeOuterLegChannel_explicit
    (τ : Triad)
    (signP signQ signK : HelicitySign) :
    threeOuterLegChannel
      modeNorm component project cross conjugate
      τ signP signQ signK =
      ((signedEigenvalue modeNorm signQ τ.q -
          signedEigenvalue modeNorm signP τ.p) •
        project τ.k
          (cross (component signP τ.p) (component signQ τ.q))) +
      ((signedEigenvalue modeNorm signQ τ.q -
          signedEigenvalue modeNorm signK τ.k) •
        project τ.p
          (cross
            (component signK τ.k)
            (conjugate (component signQ τ.q)))) +
      ((signedEigenvalue modeNorm signP τ.p -
          signedEigenvalue modeNorm signK τ.k) •
        project τ.q
          (cross
            (component signK τ.k)
            (conjugate (component signP τ.p)))) := rfl

end Vector


section PairingNormalForm

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

variable (modeNorm : Mode → ℝ)
variable (component : HelicitySign → Mode → V)
variable (project : Mode → V → V)
variable (cross : V → V → V)
variable (conjugate : V → V)
variable (pairing : V → V → ℝ)

variable
  (pairScaleRight :
    ∀ (a : ℝ) (u v : V), pairing u (a • v) = a * pairing u v)
  (projectSelfAdjoint :
    ∀ (m : Mode) (u v : V),
      pairing u (project m v) = pairing (project m u) v)

def baseGeometry
    (test : V) (τ : Triad) (signP signQ : HelicitySign) : ℝ :=
  pairing (project τ.k test)
    (cross (component signP τ.p) (component signQ τ.q))

def pLegGeometry
    (test : V) (τ : Triad) (signK signQ : HelicitySign) : ℝ :=
  pairing (project τ.p test)
    (cross (component signK τ.k) (conjugate (component signQ τ.q)))

def qLegGeometry
    (test : V) (τ : Triad) (signK signP : HelicitySign) : ℝ :=
  pairing (project τ.q test)
    (cross (component signK τ.k) (conjugate (component signP τ.p)))

theorem basePairing_factor
    (test : V) (τ : Triad) (signP signQ : HelicitySign) :
    pairing test
      (baseChannelVector modeNorm component project cross τ signP signQ) =
      baseCoefficient modeNorm τ signP signQ *
        baseGeometry component project cross pairing test τ signP signQ := by
  unfold baseChannelVector channelVector baseGeometry baseCoefficient
  rw [pairScaleRight]
  rw [projectSelfAdjoint]

theorem pLegPairing_factor
    (test : V) (τ : Triad) (signK signQ : HelicitySign) :
    pairing test
      (pLegChannelVector
        modeNorm component project cross conjugate τ signK signQ) =
      pLegCoefficient modeNorm τ signK signQ *
        pLegGeometry component project cross conjugate pairing
          test τ signK signQ := by
  unfold pLegChannelVector pLegGeometry pLegCoefficient
  rw [pairScaleRight]
  rw [projectSelfAdjoint]

theorem qLegPairing_factor
    (test : V) (τ : Triad) (signK signP : HelicitySign) :
    pairing test
      (qLegChannelVector
        modeNorm component project cross conjugate τ signK signP) =
      qLegCoefficient modeNorm τ signK signP *
        qLegGeometry component project cross conjugate pairing
          test τ signK signP := by
  unfold qLegChannelVector qLegGeometry qLegCoefficient
  rw [pairScaleRight]
  rw [projectSelfAdjoint]

theorem geometryOrientation_closes
    (testK testP testQ : V)
    (τ : Triad)
    (signP signQ signK : HelicitySign)
    (hP :
      pLegGeometry component project cross conjugate pairing
          testP τ signK signQ =
        - baseGeometry component project cross pairing
          testK τ signP signQ)
    (hQ :
      qLegGeometry component project cross conjugate pairing
          testQ τ signK signP =
        baseGeometry component project cross pairing
          testK τ signP signQ) :
    pairing testK
        (baseChannelVector modeNorm component project cross τ signP signQ) +
      pairing testP
        (pLegChannelVector
          modeNorm component project cross conjugate τ signK signQ) +
      pairing testQ
        (qLegChannelVector
          modeNorm component project cross conjugate τ signK signP) = 0 := by
  rw [basePairing_factor modeNorm component project cross pairing
        pairScaleRight projectSelfAdjoint]
  rw [pLegPairing_factor modeNorm component project cross conjugate pairing
        pairScaleRight projectSelfAdjoint]
  rw [qLegPairing_factor modeNorm component project cross conjugate pairing
        pairScaleRight projectSelfAdjoint]
  rw [hP, hQ]
  unfold baseCoefficient pLegCoefficient qLegCoefficient
  ring

end PairingNormalForm


end CyclicHelicalVectorTransform
end NSBControl
