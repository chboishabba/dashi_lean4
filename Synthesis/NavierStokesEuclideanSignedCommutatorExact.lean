import Synthesis.NavierStokesEuclideanSignedProductMajorantExact
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! Whole-space analogue of the original periodic energy involution.
Actual Lebesgue product, not a lattice renamed R³. The ordered
advective sign is -i, and q is the differentiated frequency.
The integrability of BOTH weighted folds is retained: this identity
does not prove a global signed critical-time ceiling. -/
namespace DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory
open scoped BigOperators
noncomputable section

def continuumCell (U : Vec3 → CVec3) (p q : Vec3) : ℝ :=
  ∑ i : Fin 3, (-Complex.I*outputDot q (U p)*U q i*star (U (p+q) i)).re

theorem continuumCell_flip (U : Vec3 → CVec3)
    (ht : ∀ p,outputDot p (U p)=0)
    (hr : ∀ p i,U (-p) i=star (U p i)) (p q : Vec3) :
    continuumCell U (-p) (p+q)= -continuumCell U p q := by
  have hdot : outputDot (p+q) (U (-p))=star (outputDot q (U p)) := by
    have h : outputDot (p+q) (U p)=outputDot p (U p)+outputDot q (U p) := by
      unfold outputDot
      simp only [Pi.add_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]
    rw [ht p,zero_add] at h
    rw [← h]
    unfold outputDot
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [star_mul,hr]
    simp
  unfold continuumCell
  rw [hdot,neg_add_cancel_left,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.star_def,Complex.mul_re,Complex.mul_im]
  ring

/-- The triangular involution is measure preserving by two literal
additive Haar substitutions (q -> p+q, then p -> -p). Bochner integrals
are used, including the same sign on the actual complex Fourier cells. -/
theorem continuum_flip_iterated (f : Vec3 → Vec3 → ℝ) :
    (∫ p,∫ q,f (-p) (p+q))=∫ p,∫ q,f p q := by
  have h (p : Vec3) : (∫ q,f (-p) (p+q))=∫ q,f (-p) q :=
    integral_add_left_eq_self (f (-p)) p
  simp_rw [h]
  exact integral_neg_eq_self (fun p : Vec3=>∫ q,f p q) volume

def continuumOutputFold (w : Vec3 → ℝ) (U : Vec3 → CVec3) (a : Vec3 × Vec3) :=
  w (a.1+a.2)*continuumCell U a.1 a.2

def continuumInputFold (w : Vec3 → ℝ) (U : Vec3 → CVec3) (a : Vec3 × Vec3) :=
  w a.2*continuumCell U a.1 a.2

theorem continuum_weighted_flip (w : Vec3 → ℝ) (U : Vec3 → CVec3)
    (ht : ∀ p,outputDot p (U p)=0)
    (hr : ∀ p i,U (-p) i=star (U p i)) :
    (∫ p,∫ q,w (p+q)*continuumCell U p q)=
      -(∫ p,∫ q,w q*continuumCell U p q) := by
  have h := continuum_flip_iterated (fun p q=>w (p+q)*continuumCell U p q)
  simp only [neg_add_cancel_left,continuumCell_flip U ht hr,mul_neg,integral_neg] at h
  exact h.symm

/-- Actual joint Lebesgue signed commutator; the Fubini hypotheses
are on precisely the two original weighted cells, not a new measure.
No torus approximation or replacement of the signed density. -/
theorem continuum_signed_commutator (w : Vec3 → ℝ) (U : Vec3 → CVec3)
    (ht : ∀ p,outputDot p (U p)=0)
    (hr : ∀ p i,U (-p) i=star (U p i))
    (ho : Integrable (continuumOutputFold w U) (volume.prod volume))
    (hi : Integrable (continuumInputFold w U) (volume.prod volume)) :
    2*(∫ a,continuumOutputFold w U a ∂(volume.prod volume))=
      ∫ a,(w (a.1+a.2)-w a.2)*continuumCell U a.1 a.2 ∂(volume.prod volume) := by
  have h := continuum_weighted_flip w U ht hr
  have hO := integral_prod (continuumOutputFold w U) ho
  have hI := integral_prod (continuumInputFold w U) hi
  change (∫ a,continuumOutputFold w U a ∂(volume.prod volume))=
    (∫ p,∫ q,w (p+q)*continuumCell U p q) at hO
  change (∫ a,continuumInputFold w U a ∂(volume.prod volume))=
    (∫ p,∫ q,w q*continuumCell U p q) at hI
  have he : (fun a : Vec3×Vec3=>(w (a.1+a.2)-w a.2)*continuumCell U a.1 a.2)=
    fun a=>continuumOutputFold w U a-continuumInputFold w U a := by
    funext a
    simp [continuumOutputFold,continuumInputFold,sub_mul]
  rw [he,integral_sub ho hi,hO,hI]
  linarith

end
end DASHI.NavierStokes.EuclideanMidpoint
