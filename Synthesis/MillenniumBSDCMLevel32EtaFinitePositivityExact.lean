import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Selected CM curve: positive finite q-products for the level-32 newform

Original analytic source:
f_32(z) = eta(4z)^2 * eta(8z)^2,
the normalized weight-two newform of conductor 32, whose
L-function matches y²=x³-x (LMFDB 32.2.a.a).
A published exact evaluation gives
  L(f_32,1) = 2^(-7/2) * Beta(1/4,1/4) > 0.
See: Huber–Liu–McLaughlin–Ye–Yuan–Zhang,
Computing Special L-Values of Certain Modular Forms with CM,
Lemma 3.1 (https://emis.de/ft/24022).

For real q in (0,1), eta(4it)^2 eta(8it)^2 has the
positive q-product q * product_{n>=1}
  (1-q^(4n))^2 * (1-q^(8n))^2.

This file implements its ACTUAL FINITE TRUNCATION and proves
strict positivity at every finite cutoff. It does NOT identify
its infinite limit with an elliptic L-function or prove the
central-value integral is positive; the uniform/infinite
product lower bound, Mellin transform and same-curve modular
identification remain K4 mathematical gates.
-/

namespace Synthesis.Millennium.BSD

/-- Original level-32 eta-product finite truncation in q=e^{-2πt},
using exactly the exponents from eta(4τ)^2 eta(8τ)^2. -/
def cmLevel32EtaProductTruncation (q : ℝ) (N : ℕ) : ℝ :=
  q * ∏ n ∈ Finset.range N,
    (1 - q ^ (4 * (n + 1))) ^ 2 *
      (1 - q ^ (8 * (n + 1))) ^ 2

/-- Every finite eta-product truncation is strictly positive on
the actual imaginary-axis domain 0<q<1. -/
theorem cmLevel32EtaProductTruncation_pos
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    0 < cmLevel32EtaProductTruncation q N := by
  unfold cmLevel32EtaProductTruncation
  apply mul_pos hq0
  apply Finset.prod_pos
  intro n hn
  have h4n : 4 * (n + 1) ≠ 0 := by omega
  have h8n : 8 * (n + 1) ≠ 0 := by omega
  have h4 : 0 < 1 - q ^ (4 * (n + 1)) :=
    sub_pos.mpr (pow_lt_one₀ hq0.le hq1 h4n)
  have h8 : 0 < 1 - q ^ (8 * (n + 1)) :=
    sub_pos.mpr (pow_lt_one₀ hq0.le hq1 h8n)
  exact mul_pos (pow_pos h4 _) (pow_pos h8 _)

/-- The empty eta-product truncation is precisely q, a same-object
sanity check on the conductor-32 leading Fourier term. -/
theorem cmLevel32EtaProductTruncation_zero (q : ℝ) :
    cmLevel32EtaProductTruncation q 0 = q := by
  simp [cmLevel32EtaProductTruncation]

/-- At any finite cutoff positivity is independent of the
previous truncation; this theorem makes no false lower-bound
claim for the infinite product. -/
theorem cmLevel32EtaProductTruncation_pair_pos
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m n : ℕ) :
    0 < cmLevel32EtaProductTruncation q m ∧
      0 < cmLevel32EtaProductTruncation q n :=
  ⟨cmLevel32EtaProductTruncation_pos hq0 hq1 m,
   cmLevel32EtaProductTruncation_pos hq0 hq1 n⟩

end Synthesis.Millennium.BSD
