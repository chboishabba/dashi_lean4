import BishopZ7Admission
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Z7 -> genuine convergent Dirichlet series, SAME pinned Mathlib object

External theorem (NOT by DASHI): Shawn Krisman, telaviv/zeta-irrationality,
v1.0, ZetaIrr.Z7.oneOfZeta7To21; mathematics in the Ball--Rivoal,
Rivoal and Zudilin lineage. Mathlib owns the zeta-to-Dirichlet theorem.

DASHI contribution: discharge the explicit same-value input in
BishopZ7Admission.z7WitnessForSource with Mathlib's actual
zeta_eq_tsum_one_div_nat_add_one_cpow. This is a mathematical Dirichlet
series, not a synthetic value function and not the original Agda
Bishop-real series. The external theorem remains a kernel import,
not a chosen numerical index.

This isolated project targets Lean v4.35.0 and ZetaIrrational v1.0,
avoiding an invalid .olean import from dashi_lean4 root's older Mathlib.
It does not identify this sidecar Dirichlet series with the root's
source definition across versions, or with vendored Agda Bishop reals.
Local Lake build and axiom audit MUST succeed before kernel promotion.
-/

namespace BishopZ7DirichletSameObject

noncomputable section

/-- Literal complex Dirichlet coefficients (n+1)^(-s), not an opaque
value carrier. The starting index n=0 corresponds to positive integer 1. -/
def selectedDirichlet (s : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s

/-- Exact equality on Re(s)>1 with the genuine Mathlib riemannZeta. -/
theorem selectedDirichlet_eq_riemannZeta
    (s : ℂ) (hs : 1 < s.re) :
    selectedDirichlet s = riemannZeta s := by
  unfold selectedDirichlet
  exact (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm

theorem selectedOddDirichlet_eq_riemannZeta
    (k : Fin 15) :
    selectedDirichlet ((5 + 2 * k.val : ℕ) : ℂ) =
      riemannZeta ((5 + 2 * k.val : ℕ) : ℂ) := by
  apply selectedDirichlet_eq_riemannZeta
  have hnat : 1 < 5 + 2 * k.val := by omega
  have hreal : (1 : ℝ) < ((5 + 2 * k.val : ℕ) : ℝ) :=
    by exact_mod_cast hnat
  simpa using hreal

/-- Unconditional relative to the admitted *external imported theorem*:
there exists an original value in the 15-index positive-odd
Dirichlet series which cannot equal any rational complex cast.
The proof does not compute which index satisfies the disjunction. -/
theorem z7DirichletOddWindowIsIrrational :
    ∃ k : Fin 15,
      ¬ ∃ q : ℚ,
        selectedDirichlet ((5 + 2 * k.val : ℕ) : ℂ) = (q : ℂ) := by
  exact BishopZ7Admission.z7WitnessForSource
    (fun k : Fin 15 =>
      selectedDirichlet ((5 + 2 * k.val : ℕ) : ℂ))
    selectedOddDirichlet_eq_riemannZeta

#print axioms selectedDirichlet_eq_riemannZeta
#print axioms selectedOddDirichlet_eq_riemannZeta
#print axioms z7DirichletOddWindowIsIrrational

end
end BishopZ7DirichletSameObject
