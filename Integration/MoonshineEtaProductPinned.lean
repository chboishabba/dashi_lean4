import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# Unit-disc Euler product helpers at the pinned Mathlib version

These lemmas were packaged into DedekindEta only after the repository's
v4.28.0 pin, but their proofs use APIs already present at the pin.  They are
ported locally because the eta^24 q-expansion coefficient proof needs the
Euler product as a differentiable function of q near 0.
-/

namespace Integration.MoonshineEtaProductPinned

open Complex
open scoped Topology

noncomputable section

theorem multipliable_one_sub_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
  apply multipliable_one_add_of_summable
    (f := fun n ↦ -q ^ (n + 1))
  simpa using
    (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (norm_nonneg _) hq)

theorem multipliableLocallyUniformlyOn_one_sub_pow :
    MultipliableLocallyUniformlyOn
      (fun n q : ℂ ↦ 1 - q ^ (n + 1))
      (Metric.ball (0 : ℂ) 1) := by
  use fun q ↦ ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN]
      using tendstoUniformlyOn_empty
  · obtain ⟨q₀, hq₀, _, HB⟩ :=
      hcK.exists_sSup_image_eq_and_ge hN
        (show ContinuousOn (fun q : ℂ ↦ ‖q‖) K by fun_prop)
    refine
      ((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one (norm_nonneg _)
          (by
            simpa [Metric.mem_ball, dist_zero_right]
              using hK hq₀))).hasProdUniformlyOn_nat_one_add
        hcK (.of_forall fun n x hx ↦ ?_)
        (fun _ ↦ by fun_prop)
    simpa using
      pow_le_pow_left₀ (norm_nonneg _) (HB x hx) (n + 1)

theorem differentiableOn_tprod_one_sub_pow :
    DifferentiableOn ℂ
      (fun q ↦ ∏' n, (1 - q ^ (n + 1)))
      (Metric.ball (0 : ℂ) 1) :=
  multipliableLocallyUniformlyOn_one_sub_pow
    |>.hasProdLocallyUniformlyOn
    |>.differentiableOn
      (.of_forall fun _ ↦ by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finset_prod (by fun_prop))
      Metric.isOpen_ball

theorem differentiableOn_tprod_one_sub_pow_pow (k : ℕ) :
    DifferentiableOn ℂ
      (fun q ↦ ∏' n, (1 - q ^ (n + 1)) ^ k)
      (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun _ hq ↦
    (multipliable_one_sub_pow (by simpa using hq)).tprod_pow k

structure Boundary where
  unitDiscMultipliabilityOwned : Bool
  locallyUniformProductOwned : Bool
  productDifferentiabilityOwned : Bool
  poweredProductDifferentiabilityOwned : Bool
  dependencyBumpUsed : Bool

def boundary : Boundary where
  unitDiscMultipliabilityOwned := true
  locallyUniformProductOwned := true
  productDifferentiabilityOwned := true
  poweredProductDifferentiabilityOwned := true
  dependencyBumpUsed := false

end

end Integration.MoonshineEtaProductPinned
