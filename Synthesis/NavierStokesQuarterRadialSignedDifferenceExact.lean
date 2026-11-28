import Synthesis.NavierStokesActualFractionalCommutatorExact
import Synthesis.NavierStokesEuclideanSignedCommutatorExact

/-! Actual N2e quarter-weight divided difference, on the same
three Cartesian coordinates for A and the original lattice embedding
for B. No denominator at equal radial frequencies is introduced.
The signed numerator is the literal radial change, including the
angle between p and q. This is a commutator geometry identity, not
a cutoff-uniform bound on its time integral. -/
namespace DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

def radialMass (p : Vec3) : ℝ := Real.sqrt (massSq p)
def quarterRadial (p : Vec3) : ℝ := Real.sqrt (radialMass p)
def spatialDot (p q : Vec3) : ℝ := ∑ i : Fin 3,p i*q i

theorem radialMass_sq (p : Vec3) : radialMass p^2=massSq p :=
  Real.sq_sqrt (massSq_nonnegative p)

theorem quarterRadial_sq (p : Vec3) : quarterRadial p^2=radialMass p :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem massSq_add_change (p q : Vec3) :
    massSq (p+q)-massSq q=massSq p+2*spatialDot p q := by
  unfold massSq spatialDot
  simp only [Fin.sum_univ_three,Pi.add_apply]
  ring

theorem quarterRadial_signed_product (p q : Vec3) :
    (quarterRadial (p+q)-quarterRadial q)*
      (quarterRadial (p+q)+quarterRadial q)*
      (radialMass (p+q)+radialMass q)=massSq p+2*spatialDot p q := by
  calc
    _ = (quarterRadial (p+q)^2-quarterRadial q^2)*
      (radialMass (p+q)+radialMass q) := by ring
    _ = radialMass (p+q)^2-radialMass q^2 := by
      rw [quarterRadial_sq,quarterRadial_sq]
      ring
    _ = _ := by rw [radialMass_sq,radialMass_sq,massSq_add_change]

theorem quarterRadial_signed_divided_difference (p q : Vec3)
    (h : 0<radialMass (p+q)+radialMass q) :
    quarterRadial (p+q)-quarterRadial q=
      (massSq p+2*spatialDot p q)/
        ((quarterRadial (p+q)+quarterRadial q)*(radialMass (p+q)+radialMass q)) := by
  have hq0 : 0≤quarterRadial (p+q) := Real.sqrt_nonneg _
  have hq1 : 0≤quarterRadial q := Real.sqrt_nonneg _
  have hs : 0<quarterRadial (p+q)+quarterRadial q := by
    by_contra! hn
    have h0 : quarterRadial (p+q)=0 := by linarith
    have h1 : quarterRadial q=0 := by linarith
    rw [← quarterRadial_sq (p+q),← quarterRadial_sq q,h0,h1] at h
    norm_num at h
  apply (eq_div_iff (ne_of_gt (mul_pos hs h))).mpr
  rw [← mul_assoc,quarterRadial_signed_product]

/-- The sign of the weight difference is exactly the sign of the
physical radial numerator, including the zero-angle cancellation.
This proof includes the double-zero radius without division. -/
theorem quarterRadial_sign_bidi (p q : Vec3) :
    (0≤quarterRadial (p+q)-quarterRadial q ↔
      0≤massSq p+2*spatialDot p q) ∧
    (quarterRadial (p+q)-quarterRadial q=0 ↔
      massSq p+2*spatialDot p q=0) := by
  have h₁ := quarterRadial_sq (p+q)
  have h₂ := quarterRadial_sq q
  have h₃ := radialMass_sq (p+q)
  have h₄ := radialMass_sq q
  have hn₁ : 0≤quarterRadial (p+q) := Real.sqrt_nonneg _
  have hn₂ : 0≤quarterRadial q := Real.sqrt_nonneg _
  have hr₁ : 0≤radialMass (p+q) := Real.sqrt_nonneg _
  have hr₂ : 0≤radialMass q := Real.sqrt_nonneg _
  rw [← massSq_add_change]
  constructor
  · rw [sub_nonneg,sub_nonneg,← h₃,← h₄]
    rw [sq_le_sq₀ hr₂ hr₁,← h₁,← h₂,sq_le_sq₀ hn₂ hn₁]
  · rw [sub_eq_zero,sub_eq_zero,← h₃,← h₄]
    constructor
    · intro h
      rw [← h₁,← h₂,h]
    · intro h
      have he : radialMass (p+q)=radialMass q := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h|h
        · exact h
        · linarith
      rw [← h₁,← h₂] at he
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h|h
      · exact h
      · linarith

end
end DASHI.NavierStokes.EuclideanMidpoint

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint

theorem originalQuarterWeight_signed_product (p q : Lattice) :
    (quarterWeight (p+q)-quarterWeight q)*
      (quarterWeight (p+q)+quarterWeight q)*
      (radialMass (embedMode (p+q))+radialMass (embedMode q))=
        massSq (embedMode p)+2*spatialDot (embedMode p) (embedMode q) := by
  have he : embedMode (p+q)=embedMode p+embedMode q := by
    funext i
    simp [embedMode]
  unfold quarterWeight
  rw [he]
  exact quarterRadial_signed_product (embedMode p) (embedMode q)

end DASHI.NavierStokes.PhysicalMixed
