import Mathlib
import Integration.Variation.Pairing
import Integration.Variation.CutoffLimit
import Integration.Variation.CommonLanguage

/-!
# QFT/GR frontier — the smallest theorem cutset, assembled

The three preceding lanes are the pieces the live frontier asks for.  This file
puts them together into a single statement, so that the exact list of remaining
*inputs* is visible as the hypothesis list of one theorem.

```
        one common action, one common perturbation fibre
                        |
   GR receipt:   δ_g S_common[h] = ⟨G, h⟩
   QFT receipts: δ_g S_k^(i)[h]  = ⟨T_k^(i), h⟩          (finite cutoff, sectorwise)
   cutoff limit: δ_g S_k^(i)[h]  → δ_g S_∞^(i)[h]
   aggregation:  δ_g S_common[h] = Σ_i δ_g S_∞^(i)[h]
   fibre:        the admitted perturbations are dense
                        |
                        v
   unique continuum sector stresses T_c^(i), and  G = Σ_i T_c^(i)
```

`qftgr_stress_weld_of_cutset` is that implication, proved.  Everything above the
line is a hypothesis: this file does *not* prove that any physical theory
satisfies any of them, and no such claim is made anywhere in this lane.  What it
does prove is that these five inputs — and no further architecture — suffice,
and (via the negatives in the three lanes) that dropping the density
hypothesis, the equal-carrier hypothesis, the convergence hypothesis or the
aggregation step breaks the conclusion.
-/

namespace Integration.Variation.Weld

open scoped InnerProductSpace RealInnerProductSpace
open Filter Integration.Variation.Pairing Integration.Variation.CutoffLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The assembled QFT/GR stress weld.**

Inputs: one common variation `deltaCommon` of one common action; a GR receipt
representing it by `G` on the admitted fibre; finite-cutoff sectorwise receipts
representing each sector's cutoff variation by a finite stress `T i k`;
convergence of each sector's cutoff variation; the aggregation identity; and a
dense admitted fibre.

Output: each sector has a unique continuum stress `Tc i` representing its
continuum variation, and the GR tensor equals the aggregated continuum QFT
stress. -/
theorem qftgr_stress_weld_of_cutset [CompleteSpace H] {ι : Type*} (s : Finset ι)
    (K : Submodule ℝ H) (hdense : Dense (K : Set H))
    (deltaCommon : H → ℝ) (G : H)
    (hGR : ∀ h ∈ K, deltaCommon h = pair G h)
    (deltaSecK : ι → ℕ → H → ℝ) (T : ι → ℕ → H)
    (hfin : ∀ i ∈ s, ∀ k h, deltaSecK i k h = pair (T i k) h)
    (deltaSecInf : ι → H → ℝ)
    (hconv : ∀ i ∈ s, ∀ h, Tendsto (fun k => deltaSecK i k h) atTop (nhds (deltaSecInf i h)))
    (hagg : ∀ h ∈ K, deltaCommon h = ∑ i ∈ s, deltaSecInf i h) :
    ∃ Tc : ι → H,
      (∀ i ∈ s, ∀ h, deltaSecInf i h = pair (Tc i) h) ∧
      (∀ h ∈ K, deltaCommon h = pair (∑ i ∈ s, Tc i) h) ∧
      G = ∑ i ∈ s, Tc i := by
  have hsec : ∀ i, ∃ Tci : H, i ∈ s → ∀ h, deltaSecInf i h = pair Tci h := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨Tci, hTci, -⟩ :=
        continuum_stress_of_cutoff_family (deltaSecK i) (T i) (deltaSecInf i)
          (fun k h => hfin i hi k h) (hconv i hi)
      exact ⟨Tci, fun _ => hTci⟩
    · exact ⟨0, fun hi' => absurd hi' hi⟩
  choose Tc hTc using hsec
  have hTc' : ∀ i ∈ s, ∀ h, deltaSecInf i h = pair (Tc i) h := fun i hi => hTc i hi
  have htotal : ∀ h ∈ K, deltaCommon h = pair (∑ i ∈ s, Tc i) h := by
    intro h hh
    rw [hagg h hh, pair_sum]
    exact Finset.sum_congr rfl fun i hi => hTc' i hi h
  refine ⟨Tc, hTc', htotal, ?_⟩
  refine eq_of_pair_eq_on_dense_submodule G (∑ i ∈ s, Tc i) K hdense (fun v hv => ?_)
  rw [← hGR v hv, htotal v hv]

/-- The same conclusion read as the physical statement it encodes: on the
admitted fibre the continuum variation of the common action is represented by
the Einstein tensor *and* by the aggregated continuum stress, and these are the
same tensor. -/
theorem common_variation_has_one_stress [CompleteSpace H] {ι : Type*} (s : Finset ι)
    (K : Submodule ℝ H) (hdense : Dense (K : Set H))
    (deltaCommon : H → ℝ) (G : H)
    (hGR : ∀ h ∈ K, deltaCommon h = pair G h)
    (deltaSecK : ι → ℕ → H → ℝ) (T : ι → ℕ → H)
    (hfin : ∀ i ∈ s, ∀ k h, deltaSecK i k h = pair (T i k) h)
    (deltaSecInf : ι → H → ℝ)
    (hconv : ∀ i ∈ s, ∀ h, Tendsto (fun k => deltaSecK i k h) atTop (nhds (deltaSecInf i h)))
    (hagg : ∀ h ∈ K, deltaCommon h = ∑ i ∈ s, deltaSecInf i h) :
    ∃ Tc : ι → H, G = ∑ i ∈ s, Tc i ∧
      ∀ h ∈ K, deltaCommon h = pair G h ∧ pair G h = pair (∑ i ∈ s, Tc i) h := by
  obtain ⟨Tc, -, htotal, hweld⟩ :=
    qftgr_stress_weld_of_cutset s K hdense deltaCommon G hGR deltaSecK T hfin
      deltaSecInf hconv hagg
  refine ⟨Tc, hweld, fun h hh => ⟨hGR h hh, ?_⟩⟩
  rw [hweld]

end Integration.Variation.Weld
