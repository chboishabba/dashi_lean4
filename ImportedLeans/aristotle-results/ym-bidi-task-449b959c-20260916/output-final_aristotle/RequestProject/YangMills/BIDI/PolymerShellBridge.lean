/-
# Working backwards: the geometric shell estimate (32) from the polymer machinery

The assembled chain (`BIDI.Assembly`) consumes the geometric shell estimate

    C_Cauchy · M_shell ≤ C · e^{-m d_phys}                              (32)

as an input.  This file discharges it from material that is already proved in
this library: `YangMills.shell_energy_geometric` (RowBShellEnergy) turns an
exponential activity majorant and a polymer entropy bound into the geometric
shell energy `E_n ≤ (A·B) r^n`, `r = e^{ν−μ} < 1`.

What is added here is the *far*-shell tail, which is what the spatial estimate
at physical separation `d` actually needs:

* `far_shell_energy_tsum_le` — the total energy carried by all shells at
  distance at least `d` obeys

      Σ_{n ≥ d} E_n ≤ (A·B)/(1 − r) · e^{−(μ−ν)d},

  i.e. a geometric spatial estimate with mass `m = μ − ν > 0`;
* `cauchy_shell_estimate_of_polymer` — multiplied by the Cauchy constant, this
  is literally hypothesis `hgeom` of
  `mixedLog_bound_of_source_data`, with `C = C_Cauchy·A·B/(1−r)` and `m = μ−ν`.

So the geometric input of §11 is no longer a free constant of the BIDI chain: it
is the polymer decay rate minus the polymer entropy rate.  The two polymer
inputs themselves (activity majorant, entropy bound) remain hypotheses, exactly
as recorded in `RowBShellEnergy`.
-/
import Mathlib
import RequestProject.YangMills.RowBShellEnergy
import RequestProject.YangMills.BIDI.CauchyMixed

namespace RequestProject.YangMills.BIDI

open Finset _root_.YangMills

variable {X : Type*}

theorem far_shell_energy_tsum_le {shell : ℕ → Finset X} {act : X → ℝ}
    {A B mu nu : ℝ}
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmn : nu < mu) (d : ℕ) :
    ∑' n : ℕ, (∑ x ∈ shell (d + n), |act x|)
      ≤ ((A * B) / (1 - shellRatio nu mu)) * Real.exp (-((mu - nu) * d)) := by
  set r := shellRatio nu mu with hr
  have hr0 : 0 ≤ r := shellRatio_nonneg nu mu
  have hr1 : r < 1 := shellRatio_lt_one hmn
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hterm : ∀ n : ℕ, (∑ x ∈ shell (d + n), |act x|) ≤ ((A * B) * r ^ d) * r ^ n := by
    intro n
    have h := shell_energy_geometric hact hcard hA (d + n)
    calc ∑ x ∈ shell (d + n), |act x| ≤ (A * B) * r ^ (d + n) := h
      _ = ((A * B) * r ^ d) * r ^ n := by rw [pow_add]; ring
  have hgeo : Summable fun n : ℕ => ((A * B) * r ^ d) * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsum : Summable fun n : ℕ => ∑ x ∈ shell (d + n), |act x| :=
    Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun x _ => abs_nonneg _)
      hterm hgeo
  have hle : ∑' n : ℕ, (∑ x ∈ shell (d + n), |act x|)
      ≤ ∑' n : ℕ, ((A * B) * r ^ d) * r ^ n :=
    hsum.tsum_le_tsum hterm hgeo
  have hgeoval : ∑' n : ℕ, ((A * B) * r ^ d) * r ^ n = ((A * B) * r ^ d) / (1 - r) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    ring
  have hrd : r ^ d = Real.exp (-((mu - nu) * d)) := by
    rw [hr, shellRatio, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hgeoval, hrd] at hle
  calc ∑' n : ℕ, (∑ x ∈ shell (d + n), |act x|)
      ≤ (A * B) * Real.exp (-((mu - nu) * d)) / (1 - r) := hle
    _ = ((A * B) / (1 - r)) * Real.exp (-((mu - nu) * d)) := by ring

theorem cauchy_shell_estimate_of_polymer {shell : ℕ → Finset X} {act : X → ℝ}
    {A B mu nu rad Mshell : ℝ} (hrad : 0 < rad)
    (hact : ∀ n, ∀ x ∈ shell n, |act x| ≤ A * Real.exp (-(mu * n)))
    (hcard : ∀ n, ((shell n).card : ℝ) ≤ B * Real.exp (nu * n))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmn : nu < mu) (d : ℕ)
    (hMshell : Mshell ≤ ∑' n : ℕ, (∑ x ∈ shell (d + n), |act x|)) :
    cauchyConst rad * Mshell
      ≤ (cauchyConst rad * ((A * B) / (1 - shellRatio nu mu)))
          * Real.exp (-((mu - nu) * d)) := by
  have hc : 0 ≤ cauchyConst rad := le_of_lt (cauchyConst_pos hrad)
  have h := le_trans hMshell (far_shell_energy_tsum_le hact hcard hA hB hmn d)
  calc cauchyConst rad * Mshell
      ≤ cauchyConst rad * (((A * B) / (1 - shellRatio nu mu))
          * Real.exp (-((mu - nu) * d))) := by
        exact mul_le_mul_of_nonneg_left h hc
    _ = (cauchyConst rad * ((A * B) / (1 - shellRatio nu mu)))
          * Real.exp (-((mu - nu) * d)) := by ring

end RequestProject.YangMills.BIDI
