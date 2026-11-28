import Synthesis.MillenniumHodgeDicksonLocalizedBaseReceiverExact

namespace DASHI.Hodge.DicksonCoupled
noncomputable section

abbrev FoldPoly := MvPolynomial Address CoupledSurfaceBase
def originalFoldIdeal : Ideal FoldPoly := coupledFoldIdeal baseA baseX baseEta

def originalFoldToOpen : FoldPoly →+* ActualSourceOpen :=
  (algebraMap ActualCoupledFoldAlgebra ActualSourceOpen).comp
    (Ideal.Quotient.mk originalFoldIdeal)

/-- The actual schematic closure ideal in the original affine ambient
ring, not a reduced set of selected geometric points. -/
def actualAffineClosureIdeal : Ideal FoldPoly :=
  RingHom.ker originalFoldToOpen

theorem actual_source_zero_iff_power (a : ActualCoupledFoldAlgebra) :
    algebraMap ActualCoupledFoldAlgebra ActualSourceOpen a=0 ↔
      ∃ n : ℕ, chartDenominator^n*a=0 := by
  rw [← map_zero (algebraMap ActualCoupledFoldAlgebra ActualSourceOpen)]
  rw [IsLocalization.eq_iff_exists (Submonoid.powers chartDenominator) ActualSourceOpen]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨n,hn⟩ := c.property
    exact ⟨n,by simpa [hn] using hc⟩
  · rintro ⟨n,hn⟩
    exact ⟨⟨chartDenominator^n,⟨n,rfl⟩⟩,by simpa using hn⟩

/-- For any actual polynomial lift of the chart denominator, the kernel
is literally I : d^∞. This retains nilpotents away from the puncture. -/
theorem actual_affine_saturation (D p : FoldPoly)
    (hD : Ideal.Quotient.mk originalFoldIdeal D=chartDenominator) :
    p∈actualAffineClosureIdeal ↔
      ∃ n : ℕ, D^n*p∈originalFoldIdeal := by
  change originalFoldToOpen p=0 ↔ _
  change algebraMap ActualCoupledFoldAlgebra ActualSourceOpen
    (Ideal.Quotient.mk originalFoldIdeal p)=0 ↔ _
  rw [actual_source_zero_iff_power]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa [map_mul,map_pow,hD] using hn
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    simpa [map_mul,map_pow,hD] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hn :
        Ideal.Quotient.mk originalFoldIdeal (D^n*p)=0)

/-- An actual lift exists by the original quotient presentation.
The projective ambient homogenization is still a separate step. -/
theorem actual_affine_closure_saturation :
    ∃ D : FoldPoly, Ideal.Quotient.mk originalFoldIdeal D=chartDenominator ∧
      ∀ p, p∈actualAffineClosureIdeal ↔ ∃ n : ℕ,D^n*p∈originalFoldIdeal := by
  obtain ⟨D,hD⟩ := Ideal.Quotient.mk_surjective chartDenominator
  exact ⟨D,hD,fun p => actual_affine_saturation D p hD⟩

end
end DASHI.Hodge.DicksonCoupled
