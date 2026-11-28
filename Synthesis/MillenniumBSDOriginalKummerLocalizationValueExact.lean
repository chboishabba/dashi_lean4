import Synthesis.MillenniumBSDOriginalRationalKummerConnecting

/-! Original geometric-point Kummer naturality, at the actual cocycle
value. The compatible completion/closure embedding and the actual
continuous cohomology localization are still separate constructions. -/
namespace BSDCohomology
open WeierstrassCurve DASHI.BSD.OriginalH1
noncomputable section
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [Field L] [CharZero L]
variable (W : WeierstrassCurve K) [W.IsElliptic]
variable (V : WeierstrassCurve L) [V.IsElliptic]

/-- Transport the ORIGINAL half along the actual geometric point map,
rather than choosing an unrelated local half. -/
def transportOriginalHalf (f : GeometricPoint W →+ GeometricPoint V)
    {P : GeometricPoint W} (Q : GeometricHalfData W P) :
    GeometricHalfData V (f P) :=
  ⟨f Q.half, by rw [← map_nsmul, Q.double_half]⟩

/-- This is the pointwise localization square on the original cocycle,
assuming the real completion-induced map intertwines Galois actions.
No finite square-class substitution and no H1 map assumed. -/
theorem originalKummerCocycleValue_transport
    (f : GeometricPoint W →+ GeometricPoint V)
    (ρ : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup K)
    (hEquiv : ∀ (σ : Field.absoluteGaloisGroup L) (Q : GeometricPoint W),
      f (galoisPointMap W (ρ σ) Q) = galoisPointMap V σ (f Q))
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) (σ : Field.absoluteGaloisGroup L) :
    f ((kummerCocycleValue W hP Q (ρ σ)).1) =
      (kummerCocycleValue V
        (fun τ => by rw [← hEquiv τ P, hP (ρ τ)])
        (transportOriginalHalf W V f Q) σ).1 := by
  change f (galoisPointMap W (ρ σ) Q.half-Q.half) =
    galoisPointMap V σ (f Q.half)-f Q.half
  rw [map_sub,hEquiv]

end
end BSDCohomology
