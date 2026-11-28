import Synthesis.NavierStokes369PhaseMeasureWeldExact

/-!
Literal R3 double-interaction centered kernel on the shared nine-coordinate
carrier (xi,eta,eta'). Two input pairs share xi, not their individual input
rates. Reuses R290/R541, the original R291 pair rate and the near-origin
saturation owner. Real Cartesian/complex shadow of the Bishop geometry;
the original Fourier trajectory and constructive-measure attachment
remain separate. This is not a new PDE estimate.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint

abbrev Vec3 := Fin 3 → ℝ
abbrev CVec3 := Fin 3 → ℂ

def inputRate (ν : ℝ) (ξ η : Vec3) :=
  ν*(massSq η+massSq (fun i => ξ i-η i))

def outputRate (ν : ℝ) (ξ : Vec3) := ν*massSq ξ

def centeredDoubleRate (ν : ℝ) (ξ η η' : Vec3) :=
  2*ν*(massSq (fun i => η i-ξ i/2)+massSq (fun i => η' i-ξ i/2))

theorem centeredDoubleRate_nonneg (ν : ℝ) (hν : 0 ≤ ν) (ξ η η' : Vec3) :
    0 ≤ centeredDoubleRate ν ξ η η' :=
  mul_nonneg (mul_nonneg (by norm_num) hν)
    (add_nonneg (massSq_nonnegative _) (massSq_nonnegative _))

/-- Critical same-object weld: the R291 rate of TWO literal input pairs
is precisely the output heat rate plus a nonnegative centered residual. -/
theorem double_input_rate_identity (ν : ℝ) (ξ η η' : Vec3) :
    inputRate ν ξ η + inputRate ν ξ η' =
      outputRate ν ξ + centeredDoubleRate ν ξ η η' := by
  unfold inputRate outputRate centeredDoubleRate
  rw [physical_midpoint_mass_identity η ξ,
      physical_midpoint_mass_identity η' ξ]
  ring

def outputDot (ξ : Vec3) (u : CVec3) : ℂ :=
  ∑ i : Fin 3, (ξ i : ℂ)*u i

def rawConvection (ξ : Vec3) (u v : CVec3) : CVec3 :=
  fun i => Complex.I * outputDot ξ u * v i

def projectedConvection (ξ : Vec3) (u v : CVec3) : CVec3 :=
  fun i => rawConvection ξ u v i -
    (ξ i : ℂ) * outputDot ξ (rawConvection ξ u v) / (massSq ξ : ℂ)

/-- The explicit projected convection is output transverse for each
punctured output. No projection theorem for an unrelated field assumed. -/
theorem projectedConvection_transverse (ξ : Vec3) (u v : CVec3)
    (hξ : massSq ξ ≠ 0) :
    outputDot ξ (projectedConvection ξ u v)=0 := by
  have hn : (massSq ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  unfold outputDot projectedConvection
  simp only [Fin.sum_univ_three]
  unfold massSq at hn ⊢
  simp only [Fin.sum_univ_three] at hn ⊢
  push_cast at hn ⊢
  field_simp [hn] <;> ring

/-- The original signed Gram uses the two independently projected
divergence-form convection cells on one physical output. The velocity
function is evaluated at all four literal input frequencies. -/
def projectedDoubleGram (U : Vec3 → CVec3) (ξ η η' : Vec3) : ℝ :=
  let A := projectedConvection ξ (U η) (U (fun i => ξ i-η i))
  let B := projectedConvection ξ (U η') (U (fun i => ξ i-η' i))
  2 * ∑ i : Fin 3, ((A i)*star (B i)).re

def actualPairResolvent (ν : ℝ) (ξ η η' : Vec3) : ℝ :=
  1 / (inputRate ν ξ η + inputRate ν ξ η')

def actualOutputResolvent (ν : ℝ) (ξ : Vec3) : ℝ :=
  1 / outputRate ν ξ

def centeredCoefficient (ν : ℝ) (ξ η η' : Vec3) : ℝ :=
  actualPairResolvent ν ξ η η' * actualOutputResolvent ν ξ *
    centeredDoubleRate ν ξ η η'

/-- Exact coefficient equality required by the original
PhysicalKernelSaturationOriginWeld, specialized to the actual two rates. -/
theorem centeredCoefficient_eq_saturation (ν : ℝ) (ξ η η' : Vec3)
    (hν : 0 < ν) (hξ : 0 < massSq ξ) :
    centeredCoefficient ν ξ η η' =
      centeredDoubleRate ν ξ η η' /
        (outputRate ν ξ * (outputRate ν ξ+centeredDoubleRate ν ξ η η')) := by
  have ha : 0 < outputRate ν ξ := mul_pos hν hξ
  have hs := centeredDoubleRate_nonneg ν hν.le ξ η η'
  have hb : 0 < outputRate ν ξ+centeredDoubleRate ν ξ η η' := by linarith
  unfold centeredCoefficient actualPairResolvent actualOutputResolvent
  rw [double_input_rate_identity]
  field_simp [ne_of_gt ha,ne_of_gt hb] <;> ring

/-- Full signed kernel split with no absolute value or phase replacement. -/
theorem actual_centered_signed_gram_split (ν : ℝ) (ξ η η' : Vec3)
    (U : Vec3 → CVec3) (hν : 0 < ν) (hξ : 0 < massSq ξ) :
    actualPairResolvent ν ξ η η' * projectedDoubleGram U ξ η η' =
      actualOutputResolvent ν ξ * projectedDoubleGram U ξ η η' -
        centeredCoefficient ν ξ η η' * projectedDoubleGram U ξ η η' := by
  have ha : 0 < outputRate ν ξ := mul_pos hν hξ
  have hs := centeredDoubleRate_nonneg ν hν.le ξ η η'
  have hb : 0 < outputRate ν ξ+centeredDoubleRate ν ξ η η' := by linarith
  rw [centeredCoefficient_eq_saturation ν ξ η η' hν hξ]
  unfold actualPairResolvent actualOutputResolvent
  rw [double_input_rate_identity]
  field_simp [ne_of_gt ha,ne_of_gt hb] <;> ring

/-- Rate-only saturation bound uses s/(a+s)≤1, while keeping the
signed Gram separate. Valid at any positive output frequency. -/
theorem centeredCoefficient_le_outputResolvent (ν : ℝ) (ξ η η' : Vec3)
    (hν : 0 < ν) (hξ : 0 < massSq ξ) :
    centeredCoefficient ν ξ η η' ≤ actualOutputResolvent ν ξ := by
  have ha : 0 < outputRate ν ξ := mul_pos hν hξ
  have hs := centeredDoubleRate_nonneg ν hν.le ξ η η'
  have hb : 0 < outputRate ν ξ+centeredDoubleRate ν ξ η η' := by linarith
  rw [centeredCoefficient_eq_saturation ν ξ η η' hν hξ]
  unfold actualOutputResolvent
  apply (div_le_div_iff₀ (mul_pos ha hb) ha).mpr
  nlinarith only [sq_nonneg (outputRate ν ξ)]

end DASHI.NavierStokes.EuclideanMidpoint
