/-
One-sided lattice-tail / finite-retention theorem, at literal real-analytic
strength.

The Agda module `DASHI.Analysis.RiemannCenteredGridRetentionExact` records the
retention bookkeeping as an identity between natural-number ledger entries.
Here the same statement is proved for genuine real energies and genuine
infinite series:

* a two-sided lattice energy that is reflection-symmetric and vanishes at the
  centre equals twice its one-sided part (`twoSided_eq_two_mul_oneSided`);
* the one-sided part splits as a finite window plus a tail
  (`oneSided_split`);
* if the tail is dominated by the finite window, the finite `Fin d`-window
  retains at least a quarter of the full two-sided energy
  (`finite_retention`), and in particular a nonzero full energy cannot be lost
  (`finite_retention_pos`).

Applied to the centred grid of `RiemannAnalytic.PoissonExtension`, this is the
literal form of the "one-sided lattice-tail / finite-retention" obligation.
-/
import RiemannAnalytic.PoissonExtension

namespace RiemannAnalytic

open Finset

/-- A reflection-symmetric two-sided lattice energy that vanishes at the centre
is twice its one-sided part. -/
theorem twoSided_eq_two_mul_oneSided (E : ℤ → ℝ) (hE : Summable E)
    (hsymm : ∀ k : ℤ, E (-k) = E k) (h0 : E 0 = 0) :
    ∑' k : ℤ, E k = 2 * ∑' n : ℕ, E (n + 1) := by
  have hnat : Summable fun n : ℕ => E n :=
    hE.comp_injective fun a b hab => by exact_mod_cast hab
  have hnat' : Summable fun n : ℕ => E (n + 1) := by
    have : Summable fun n : ℕ => (fun m : ℕ => E m) (n + 1) :=
      (summable_nat_add_iff 1).2 hnat
    simpa using this
  have hneg : Summable fun n : ℕ => E (-((n : ℤ) + 1)) :=
    hnat'.congr fun n => (hsymm ((n : ℤ) + 1)).symm
  have hsplit := tsum_of_nat_of_neg_add_one (f := E) hnat hneg
  have hneg_eq : ∑' n : ℕ, E (-((n : ℤ) + 1)) = ∑' n : ℕ, E ((n : ℤ) + 1) :=
    tsum_congr fun n => hsymm ((n : ℤ) + 1)
  have hshift : ∑' i : ℕ, E ((i : ℤ) + 1) = ∑' i : ℕ, E ((i + 1 : ℕ) : ℤ) :=
    tsum_congr fun i => by push_cast; ring_nf
  have hzero : ∑' n : ℕ, E (n : ℤ) = ∑' n : ℕ, E ((n : ℤ) + 1) := by
    have h := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => E (n : ℤ)) 1 hnat
    simp only [Finset.sum_range_one, Nat.cast_zero] at h
    rw [← h, h0, hshift]
    ring
  rw [hsplit, hneg_eq, hzero]
  ring

/-- The one-sided energy splits into the finite window `[0, m)` and its tail. -/
theorem oneSided_split (a : ℕ → ℝ) (ha : Summable a) (m : ℕ) :
    ∑' n : ℕ, a n = (∑ n ∈ range m, a n) + ∑' n : ℕ, a (n + m) :=
  (ha.sum_add_tsum_nat_add m).symm

/-- **Finite retention.**  If the omitted one-sided tail beyond the finite
window is dominated by the retained window, then the finite window carries at
least a quarter of the full two-sided energy. -/
theorem finite_retention (a : ℕ → ℝ) (ha : Summable a) (m : ℕ)
    (hdom : ∑' n : ℕ, a (n + m) ≤ ∑ n ∈ range m, a n) :
    2 * ∑' n : ℕ, a n ≤ 4 * ∑ n ∈ range m, a n := by
  have h := oneSided_split a ha m
  nlinarith [h, hdom]

/-- Consequently a nonzero full transverse energy cannot disappear in the
finite one-sided window. -/
theorem finite_retention_pos (a : ℕ → ℝ) (ha : Summable a) (m : ℕ)
    (hdom : ∑' n : ℕ, a (n + m) ≤ ∑ n ∈ range m, a n)
    (hpos : 0 < 2 * ∑' n : ℕ, a n) :
    0 < ∑ n ∈ range m, a n := by
  have := finite_retention a ha m hdom
  linarith

/-- The transverse (imaginary-channel) energy of the `k`-th centred-grid
sample. -/
noncomputable def transverseEnergy (φ : ℝ → ℝ) (h α : ℝ) (k : ℤ) : ℝ :=
  (gridSample φ h α k).im ^ 2

/-- For a real even taper the full two-sided transverse energy of the centred
grid is twice its one-sided part: the `k = 0` sample is real and the `±k`
samples carry equal transverse energy. -/
theorem transverseEnergy_twoSided (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t)
    (h α : ℝ) (hsum : Summable (transverseEnergy φ h α)) :
    ∑' k : ℤ, transverseEnergy φ h α k
      = 2 * ∑' n : ℕ, transverseEnergy φ h α (n + 1) := by
  refine twoSided_eq_two_mul_oneSided _ hsum (fun k => ?_) ?_
  · exact gridSample_im_sq_neg φ hφ h α k
  · simp [transverseEnergy, gridSample_zero_im φ hφ h α]

/-- **Literal one-sided lattice-tail / finite-retention theorem for the centred
grid.**  If the positive-lattice tail beyond the finite window `1 ≤ k < m + 1`
is dominated by that window, then the finite window retains at least a quarter
of the full two-sided transverse energy. -/
theorem gridFiniteRetention (φ : ℝ → ℝ) (hφ : ∀ t, φ (-t) = φ t) (h α : ℝ)
    (hsum : Summable (transverseEnergy φ h α)) (m : ℕ)
    (hdom : ∑' n : ℕ, transverseEnergy φ h α (n + m + 1)
        ≤ ∑ n ∈ range m, transverseEnergy φ h α (n + 1)) :
    ∑' k : ℤ, transverseEnergy φ h α k
      ≤ 4 * ∑ n ∈ range m, transverseEnergy φ h α (n + 1) := by
  classical
  set a : ℕ → ℝ := fun n => transverseEnergy φ h α (n + 1) with ha_def
  have hnat : Summable fun n : ℕ => transverseEnergy φ h α n :=
    hsum.comp_injective fun x y hxy => by exact_mod_cast hxy
  have ha : Summable a := by
    have : Summable fun n : ℕ => (fun m : ℕ => transverseEnergy φ h α m) (n + 1) :=
      (summable_nat_add_iff 1).2 hnat
    simpa [ha_def] using this
  have hkey : ∀ n : ℕ, a (n + m) = transverseEnergy φ h α ((n : ℤ) + (m : ℤ) + 1) := by
    intro n
    simp only [ha_def]
    push_cast
    ring_nf
  have hdom' : ∑' n : ℕ, a (n + m) ≤ ∑ n ∈ range m, a n := by
    rw [tsum_congr hkey]
    exact hdom
  have := finite_retention a ha m hdom'
  rw [transverseEnergy_twoSided φ hφ h α hsum]
  simpa [ha_def] using this

end RiemannAnalytic
