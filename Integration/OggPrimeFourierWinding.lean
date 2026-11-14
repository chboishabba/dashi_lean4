import Integration.MoonshineSSP15OggAddressCodec
import Mathlib

namespace Integration.OggPrimeFourierWinding

open scoped BigOperators
open Integration.MoonshineSSP15OggAddressCodec

/-!
# Ogg-prime Fourier winding

This is the analytic/structural mirror of the finite Agda winding owner.
It reuses the merged SSP15/Ogg lane codec rather than creating a second Ogg
carrier.

For real winding frequency `ω`, each prime contributes the unit rotor

`(cos (ω p), sin (ω p))`.

The two finite sums are

`O(ω) = Σ_{p∈Ogg} rotor ω p`
`X(ω) = Σ_{q∈nonOgg} rotor ω q`

and the centered contrast is

`C(ω) = O(ω) - 3 X(ω)`.

Because there are fifteen canonical Ogg primes and five non-Ogg prime controls
under 72, the DC term cancels exactly: `C(0)=0`.

The generic `phaseIndex` / `rootRotor` layer makes the modular-residue reading
explicit at rational winding angles: a root-of-unity rotor factors through
`(k*p) % m`.  This is a finite Fourier observation, not an explanation of
Monstrous Moonshine and not an identification with the radial plot `p*exp(ip)`.
-/

/-- Canonical fifteen Ogg / Monster primes, matching the merged SSP15 codec. -/
def oggPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

/-- The five prime controls <= 71 marked non-Ogg by the Agda control matrix. -/
def nonOggPrimes : Finset ℕ := {37, 43, 53, 61, 67}

/-- The twenty primes participating in the centered comparison. -/
def analysisPrimes : Finset ℕ := oggPrimes ∪ nonOggPrimes

theorem oggPrimes_card : oggPrimes.card = 15 := by
  native_decide

theorem nonOggPrimes_card : nonOggPrimes.card = 5 := by
  native_decide

theorem ogg_nonOgg_disjoint : Disjoint oggPrimes nonOggPrimes := by
  native_decide

/-- The merged SSP15 lane's numeric prime is always in the Ogg support. -/
theorem ssp15_primeValue_mem_oggPrimes (p : SSP15Lane) :
    primeValue p ∈ oggPrimes := by
  cases p <;> native_decide

/-- Integer coefficient used by the centered Ogg-vs-control contrast. -/
def contrastCoeff (p : ℕ) : ℤ :=
  if p ∈ oggPrimes then 1 else if p ∈ nonOggPrimes then -3 else 0

/-- The coefficient signal has zero mean on the twenty-prime comparison set. -/
theorem contrast_coeff_sum_zero :
    (∑ p in analysisPrimes, contrastCoeff p) = 0 := by
  native_decide

/-- Unit-circle rotor at winding frequency `ω` and integer frequency `p`. -/
def rotor (ω : ℝ) (p : ℕ) : ℂ :=
  Complex.mk
    (Real.cos (ω * (p : ℝ)))
    (Real.sin (ω * (p : ℝ)))

theorem rotor_zero (p : ℕ) : rotor 0 p = 1 := by
  ext <;> simp [rotor]

/-- Reversing winding direction is complex conjugation: the exact chirality
reversal remembered from the winding picture. -/
theorem rotor_neg_eq_conj (ω : ℝ) (p : ℕ) :
    rotor (-ω) p = Complex.conj (rotor ω p) := by
  ext <;> simp [rotor]

/-- Ogg-prime phasor endpoint. -/
def oggSum (ω : ℝ) : ℂ :=
  ∑ p in oggPrimes, rotor ω p

/-- Non-Ogg control phasor endpoint. -/
def nonOggSum (ω : ℝ) : ℂ :=
  ∑ p in nonOggPrimes, rotor ω p

/-- Centered Ogg-vs-control phasor endpoint. -/
def contrastSum (ω : ℝ) : ℂ :=
  oggSum ω - 3 * nonOggSum ω

/-- The deliberately centered contrast removes the trivial DC/cardinality
spike exactly. -/
theorem contrastSum_zero : contrastSum 0 = 0 := by
  norm_num [contrastSum, oggSum, nonOggSum, oggPrimes, nonOggPrimes, rotor]

/-- The Ogg endpoint mirrors under reversal of winding direction. -/
theorem oggSum_neg_eq_conj (ω : ℝ) :
    oggSum (-ω) = Complex.conj (oggSum ω) := by
  simp [oggSum, rotor_neg_eq_conj]

/-- The non-Ogg control endpoint obeys the same conjugation law. -/
theorem nonOggSum_neg_eq_conj (ω : ℝ) :
    nonOggSum (-ω) = Complex.conj (nonOggSum ω) := by
  simp [nonOggSum, rotor_neg_eq_conj]

/-- Negative-frequency contrast is the conjugate of positive-frequency
contrast, so the endpoint curve has the expected mirror/chirality symmetry. -/
theorem contrastSum_neg_eq_conj (ω : ℝ) :
    contrastSum (-ω) = Complex.conj (contrastSum ω) := by
  simp [contrastSum, oggSum_neg_eq_conj, nonOggSum_neg_eq_conj]

/-! ## Rational winding / modular residue factorization -/

/-- Root-of-unity phase index at rational winding `ω = 2π k / m`. -/
def phaseIndex (m k p : ℕ) : ℕ := (k * p) % m

/-- Canonical angle representative for that modular phase index. -/
def rootAngle (m k p : ℕ) : ℝ :=
  (2 * Real.pi * (phaseIndex m k p : ℝ)) / (m : ℝ)

/-- Unit rotor represented by the modular phase index. -/
def rootRotor (m k p : ℕ) : ℂ :=
  Complex.mk (Real.cos (rootAngle m k p)) (Real.sin (rootAngle m k p))

/-- At rational winding, the represented rotor factors through the residue
index.  Thus the visualization is literally a modular-residue detector. -/
theorem rootRotor_depends_only_on_phaseIndex {m k p q : ℕ}
    (h : phaseIndex m k p = phaseIndex m k q) :
    rootRotor m k p = rootRotor m k q := by
  simp [rootRotor, rootAngle, h]

/-- The C3 specialization uses exactly three phase bins. -/
theorem c3_phaseIndex_lt_three (k p : ℕ) : phaseIndex 3 k p < 3 := by
  simpa [phaseIndex] using Nat.mod_lt (k * p) (by decide : 0 < 3)

/-! ## Claim-strength firewall -/

def radialPrimeSpiralIdentifiedWithFourierSum : Bool := false

def analyticIdentificationClaimed : Bool := false

def moonshineExplainedByObservedFourierPattern : Bool := false

theorem radialPrimeSpiralIdentifiedWithFourierSum_false :
    radialPrimeSpiralIdentifiedWithFourierSum = false := rfl

theorem analyticIdentificationClaimed_false :
    analyticIdentificationClaimed = false := rfl

theorem moonshineExplainedByObservedFourierPattern_false :
    moonshineExplainedByObservedFourierPattern = false := rfl

end Integration.OggPrimeFourierWinding
