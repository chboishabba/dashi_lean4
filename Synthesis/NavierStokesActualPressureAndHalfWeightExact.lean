import Synthesis.NavierStokesQuarterRadialSignedDifferenceExact

/-! Same-source physical pressure split and integrated subcritical
moment. The Fourier pressure coefficient is the longitudinal
quadratic scalar of the original -i convection. No separate
pressure unknown is introduced per triad. Integrated H^(1/2)
error is not a supremum-in-time continuation estimate. -/
namespace DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

def pressureCell (k : Vec3) (u v : CVec3) : ℂ :=
  -(outputDot k u*outputDot k v)/(massSq k:ℂ)

theorem projected_pressure_split (k : Vec3) (u v : CVec3) (i : Fin 3) :
    -projectedConvection k u v i =
      -rawConvection k u v i-Complex.I*(k i:ℂ)*pressureCell k u v := by
  have h : outputDot k (rawConvection k u v)=
      Complex.I*outputDot k u*outputDot k v := by
    unfold outputDot rawConvection
    simp only [Fin.sum_univ_three]
    ring
  unfold projectedConvection pressureCell
  rw [h]
  ring

theorem pressureCell_zero (k : Vec3) (u v : CVec3) (h : k=0) :
    pressureCell k u v=0 := by
  subst k
  simp [pressureCell,outputDot,massSq]

/-- The longitudinal correction has zero physical work on the same
transverse output, including the zero frequency. -/
theorem pressureCell_work_zero (k : Vec3) (u v z : CVec3)
    (hz : outputDot k z=0) :
    (∑ i : Fin 3,(-Complex.I*(k i:ℂ)*pressureCell k u v*star (z i)).re)=0 := by
  have hc : (∑ i : Fin 3,(k i:ℂ)*star (z i))=0 := by
    have hh := congrArg star hz
    simpa [outputDot,star_sum,star_mul,Complex.star_def] using hh
  have hsum : (∑ i : Fin 3,-Complex.I*(k i:ℂ)*pressureCell k u v*star (z i))=0 := by
    calc
      _ = (-Complex.I*pressureCell k u v)*(∑ i : Fin 3,(k i:ℂ)*star (z i)) := by
        simp only [Fin.sum_univ_three]
        ring
      _ = 0 := by rw [hc,mul_zero]
  have h := congrArg Complex.re hsum
  simpa [Complex.sum_re] using h

end
end DASHI.NavierStokes.EuclideanMidpoint

namespace DASHI.NavierStokes.RealContinuation
open Filter
open scoped Topology BigOperators
noncomputable section

/-- Positive series weighted by one power of the physical radius:
a uniform squared-radius moment and actual strong L² error imply
integrated H^(1/2) error tends to zero. The same index and errors
are retained; summability is paid before the infinite sum. -/
theorem integrated_half_weight_limit {I : Type*}
    (e : ℕ → I → ℝ) (r : I → ℝ) (D : ℝ)
    (he : ∀ n i,0≤e n i) (hr : ∀ i,0≤r i)
    (hs : ∀ n,Summable (e n))
    (h0 : Tendsto (fun n=>∑' i,e n i) atTop (𝓝 0))
    (hD : ∀ n (S : Finset I),∑ i ∈ S,r i^2*e n i≤D) :
    (∀ n,Summable (fun i=>r i*e n i)) ∧
      Tendsto (fun n=>∑' i,r i*e n i) atTop (𝓝 0) := by
  have hDn : 0≤D := by simpa using hD 0 ∅
  have hb (a : ℝ) (ha : 0<a) (n : ℕ) (S : Finset I) :
      (∑ i ∈ S,r i*e n i)≤a*D+(1/(4*a))*(∑' i,e n i) := by
    have hy (i : I) : r i≤a*r i^2+1/(4*a) := by
      apply (mul_le_mul_right₀ (show 0<4*a by positivity)).mp
      field_simp [ha.ne'] <;> nlinarith [sq_nonneg (2*a*r i-1)]
    calc
      _ ≤ ∑ i ∈ S,(a*r i^2+1/(4*a))*e n i :=
        Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (hy i) (he n i)
      _ = a*(∑ i ∈ S,r i^2*e n i)+(1/(4*a))*(∑ i ∈ S,e n i) := by
        simp_rw [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hD n S) ha.le)
        (mul_le_mul_of_nonneg_left ((hs n).sum_le_tsum S (fun i _=>he n i)) (by positivity))
  have hS (n : ℕ) : Summable (fun i=>r i*e n i) :=
    summable_of_sum_le (fun i=>mul_nonneg (hr i) (he n i)) (hb 1 zero_lt_one n)
  refine ⟨hS,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let a := ε/(4*(D+1))
  have ha : 0<a := by dsimp [a]; positivity
  have hda : a*D≤ε/4 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<4*(D+1))).mpr
    nlinarith
  have hε' : 0<ε*a := mul_pos hε ha
  filter_upwards [Metric.tendsto_nhds.mp h0 (ε*a) hε'] with n hn
  have hn' : (∑' i,e n i)<ε*a := by
    simpa [Real.dist_eq,abs_of_nonneg (tsum_nonneg (he n))] using hn
  have htotal : (∑' i,r i*e n i)≤a*D+(1/(4*a))*(∑' i,e n i) :=
    Real.tsum_le_of_sum_le (fun i=>mul_nonneg (hr i) (he n i)) (hb a ha n)
  have hsmall : (1/(4*a))*(∑' i,e n i)<ε/4 := by
    calc
      _ < (1/(4*a))*(ε*a) := mul_lt_mul_of_pos_left hn' (by positivity)
      _ = _ := by field_simp [ha.ne'] <;> ring
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (tsum_nonneg fun i=>mul_nonneg (hr i) (he n i))]
  linarith

end
end DASHI.NavierStokes.RealContinuation
