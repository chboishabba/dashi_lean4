import Integration.OggPrimeFourierWinding
import Mathlib

namespace Integration.OggPrimeDirichletPhase

open scoped BigOperators
open Integration.OggPrimeFourierWinding

/-!
# Ogg-prime multiplicative Dirichlet phase

This is the reusable analytic/structural mirror of the later climbing-gym
phase-control tranche.  It deliberately keeps two phase geometries distinct:

* additive prime winding: `exp(i * ω * p)`;
* multiplicative/Dirichlet phase: `p^(i t) = exp(i * t * log p)`.

The Agda/Python lane owns the empirical first-849 / held-out-zero replay,
Landau-main diagnostic residuals, Odlyzko provenance, and exhaustive 15,504
balanced-control ranks.  This Lean file owns only the shared finite analytic
carrier and exact elementary identities.

Attribution boundary:
* Landau (1911) and Gonek (1993) own the classical explicit-formula prior art
  for sums of `X^ρ` over zeta zeros;
* Durkan--Hughes--Pearce-Crump (2026, arXiv:2601.18025) own the cited modern
  generalisation context;
* none of those sources is credited with the DASHI Ogg contrast, held-out
  experiment, or any Monster interpretation.
-/

/-- The twenty-prime comparison set has the expected size. -/
theorem analysisPrimes_card : analysisPrimes.card = 20 := by
  native_decide

/-- Multiplicative unit phase `p^(i t)` represented without choosing a complex
power API: `cos(t log p) + i sin(t log p)`. -/
def dirichletRotor (t : ℝ) (p : ℕ) : ℂ :=
  Complex.mk
    (Real.cos (t * Real.log (p : ℝ)))
    (Real.sin (t * Real.log (p : ℝ)))

theorem dirichletRotor_zero (p : ℕ) : dirichletRotor 0 p = 1 := by
  ext <;> simp [dirichletRotor]

/-- Reversing the zeta ordinate conjugates the multiplicative phase. -/
theorem dirichletRotor_neg_eq_conj (t : ℝ) (p : ℕ) :
    dirichletRotor (-t) p = Complex.conj (dirichletRotor t p) := by
  ext <;> simp [dirichletRotor]

/-- Ogg part of the multiplicative contrast. -/
def dirichletOggSum (t : ℝ) : ℂ :=
  ∑ p in oggPrimes, dirichletRotor t p

/-- Non-Ogg five-prime control part. -/
def dirichletNonOggSum (t : ℝ) : ℂ :=
  ∑ p in nonOggPrimes, dirichletRotor t p

/-- The same centered `+1 / -3` comparison used by the Agda/Python phase
experiment, now on the multiplicative phase carrier. -/
def dirichletContrast (t : ℝ) : ℂ :=
  dirichletOggSum t - 3 * dirichletNonOggSum t

/-- Centering removes the trivial zero-frequency/cardinality contribution. -/
theorem dirichletContrast_zero : dirichletContrast 0 = 0 := by
  norm_num [dirichletContrast, dirichletOggSum, dirichletNonOggSum,
    dirichletRotor, oggPrimes, nonOggPrimes]

/-- The centered multiplicative contrast inherits conjugation symmetry. -/
theorem dirichletContrast_neg_eq_conj (t : ℝ) :
    dirichletContrast (-t) = Complex.conj (dirichletContrast t) := by
  simp [dirichletContrast, dirichletOggSum, dirichletNonOggSum,
    dirichletRotor_neg_eq_conj]

/-! ## Finite moment / pair-kernel surface

For a finite ordinate set, these are the theorem-facing versions of the
Python quantities

`v_p = mean p^(i gamma)`

and

`K_pq = mean p^(i gamma) * conj(q^(i gamma))`.

No empirical values are hard-coded here.
-/

/-- Unnormalised finite first moment.  The empirical producer normalises by
sample cardinality; keeping the sum primitive avoids a nonempty/division side
condition in the structural mirror. -/
def phaseMomentSum (samples : Finset ℝ) (p : ℕ) : ℂ :=
  ∑ t in samples, dirichletRotor t p

/-- Unnormalised Hermitian pair kernel. -/
def phasePairKernelSum (samples : Finset ℝ) (p q : ℕ) : ℂ :=
  ∑ t in samples, dirichletRotor t p * Complex.conj (dirichletRotor t q)

/-- Diagonal pair-kernel sum equals sample cardinality because every rotor has
unit modulus. -/
theorem phasePairKernelSum_diag (samples : Finset ℝ) (p : ℕ) :
    phasePairKernelSum samples p p = (samples.card : ℂ) := by
  simp [phasePairKernelSum, dirichletRotor, Complex.ext_iff, Real.cos_sq_add_sin_sq]

/-! ## Claim-strength / attribution firewall -/

/-- `p^(it)` is not identified with the older additive `exp(i ω p)` winding. -/
def multiplicativePhaseIdentifiedWithAdditivePrimeWinding : Bool := false

/-- Landau/Gonek are prior art for the explicit-formula normalization only;
their citation is not a Lean theorem import. -/
def landauGonekPriorArtImportedAsTheorem : Bool := false

/-- The exhaustive finite relabelling rank is not promoted to an exact p-value
without a separately established randomization/group-invariance null. -/
def exhaustiveRelabellingRankClaimedExactPValue : Bool := false

/-- The disjoint held-out Agda/Python experiment did not replicate the discovery
tail, so no Monster-specific anomaly is promoted here. -/
def heldOutMonsterSpecificAnomalyClaimed : Bool := false

def moonshineMechanismClaimed : Bool := false

def riemannHypothesisEvidenceClaimed : Bool := false

theorem multiplicativePhaseIdentifiedWithAdditivePrimeWinding_false :
    multiplicativePhaseIdentifiedWithAdditivePrimeWinding = false := rfl

theorem landauGonekPriorArtImportedAsTheorem_false :
    landauGonekPriorArtImportedAsTheorem = false := rfl

theorem exhaustiveRelabellingRankClaimedExactPValue_false :
    exhaustiveRelabellingRankClaimedExactPValue = false := rfl

theorem heldOutMonsterSpecificAnomalyClaimed_false :
    heldOutMonsterSpecificAnomalyClaimed = false := rfl

theorem moonshineMechanismClaimed_false : moonshineMechanismClaimed = false := rfl

theorem riemannHypothesisEvidenceClaimed_false :
    riemannHypothesisEvidenceClaimed = false := rfl

end Integration.OggPrimeDirichletPhase
