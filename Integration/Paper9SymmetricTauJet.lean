import Integration.Paper9CMShiftCheck
import Mathlib.Algebra.Polynomial.Roots

/-! SOURCE-WRITTEN, UNCOMPILED.
A5 uses symmetry of the actual two-point pullback in the original tau
coordinates, not a dense bivariate modular-polynomial table and not an
inverse j chart. The universal monic slice and cusp separation premises
are explicit below. -/
namespace Integration.Paper9SymmetricTauJet
open Complex UpperHalfPlane Polynomial Function
open scoped BigOperators
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9CM163CertificateConsumer

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

def rootPoly (τ : ℍ) : Polynomial ℂ :=
  ∏ i : Chart, (X-C (chartValue i τ))

theorem rootEval (τ : ℍ) (y : ℂ) :
    (rootPoly τ).eval y=actualProduct τ y := by
  simp [rootPoly,actualProduct,Polynomial.eval_prod]

theorem rootMonic (τ : ℍ) : (rootPoly τ).Monic :=
  Polynomial.monic_prod_X_sub_C (fun i : Chart => chartValue i τ) Finset.univ

theorem rootDegree (τ : ℍ) : (rootPoly τ).natDegree=42 := by
  classical
  have h (s : Finset Chart) :
      (∏ i ∈ s, (X-C (chartValue i τ))).natDegree=s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Polynomial.natDegree_mul
        (Polynomial.monic_X_sub_C _).ne_zero
        (Polynomial.monic_prod_X_sub_C (fun i => chartValue i τ) s).ne_zero,
        Polynomial.natDegree_X_sub_C,ih,Finset.card_insert_of_notMem hi]
      omega
  simpa [rootPoly,Chart] using h Finset.univ

-- 42 distinct chart values suffice because the leading coefficients
-- cancel. This is the exact place where multiplicity must not be lost.
theorem monicSliceAtSeparated (P : ℂ → Polynomial ℂ)
    (hP : ∀ y τ, (P y).eval (j τ)=actualProduct τ y)
    (hdeg : ∀ y, (P y).natDegree≤42)
    (hlead : ∀ y, (P y).coeff 42=1)
    (τ : ℍ) (hinj : Injective (fun i : Chart => chartValue i τ)) :
    P (j τ)=rootPoly τ := by
  have htop : (rootPoly τ).coeff 42=1 := by
    rw [← rootDegree τ]
    exact rootMonic τ
  let A := P (j τ)-rootPoly τ
  have hA : A.natDegree≤41 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n=42
    · subst n
      simp [A,Polynomial.coeff_sub,hlead,htop]
    · have hb : 42<n := by omega
      have h1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mp (hdeg (j τ)) n hb
      have h2 := Polynomial.natDegree_le_iff_coeff_eq_zero.mp (rootDegree τ).le n hb
      simp [A,Polynomial.coeff_sub,h1,h2]
  have hz (i : Chart) : A.eval (chartValue i τ)=0 := by
    have h1 := hP (j τ) (chartPoint i τ)
    change (P (j τ)).eval (chartValue i τ)=
      actualProduct (chartPoint i τ) (j τ) at h1
    rw [reverseRoot] at h1
    have h2 : (rootPoly τ).eval (chartValue i τ)=0 := by
      rw [rootEval]
      unfold actualProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    simp [A,Polynomial.eval_sub,h1,h2]
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero A hinj hz
    (by simpa [Chart] using (show A.natDegree<42 by omega))
  exact sub_eq_zero.mp hzero

-- Only the infinitely many j VALUES of separated original charts
-- are needed, not all tau or all charts at the CM double root.
theorem actualTwoPointSymmetry (P : ℂ → Polynomial ℂ)
    (hP : ∀ y τ, (P y).eval (j τ)=actualProduct τ y)
    (hdeg : ∀ y, (P y).natDegree≤42)
    (hlead : ∀ y, (P y).coeff 42=1)
    (hinf : Set.Infinite {x : ℂ | ∃ τ : ℍ,
      x=j τ ∧ Injective (fun i : Chart => chartValue i τ)}) :
    ∀ τ σ : ℍ, actualProduct τ (j σ)=actualProduct σ (j τ) := by
  intro τ σ
  have hpoly : P (j σ)=rootPoly σ := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinf.mono
    intro x hx
    obtain ⟨v,rfl,hv⟩ := hx
    rw [hP,rootEval]
    have he := congrArg (fun A : Polynomial ℂ => A.eval (j σ))
      (monicSliceAtSeparated P hP hdeg hlead v hv)
    rw [hP,rootEval] at he
    exact he.symm
  rw [← hP,hpoly,rootEval]

-- Direct tau-coordinate jet. A2,B2,C3,D3 are the coefficients of
-- A2(u²+v²)+B2 uv+C3(u³+v³)+D3 uv(u+v).
-- The original diagonal/fixed slice determine them without inversion.
def A2 (a S2 : ℂ) := S2*a^2
def B2 (a P2 S2 : ℂ) := (P2-2*S2)*a^2
def C3 (a b S2 S3 : ℂ) := S2*a*b+S3*a^3
def D3 (a b P2 P3 S2 S3 : ℂ) :=
  ((P2-2*S2)*a*b+(P3-2*S3)*a^3)/2

theorem tauJetToSigned (alpha a b gamma P2 P3 S2 S3 : ℂ)
    (ha : a≠0)
    (hf : 41*alpha^2+81*alpha+41=0)
    (hq : 41*P2=163*S2)
    (hc : (B2 a P2 S2+2*A2 a S2*alpha)*gamma+
      2*C3 a b S2 S3*(1+alpha^3)+
      2*D3 a b P2 P3 S2 S3*alpha*(1+alpha)=0) :
    163*S2*((alpha^2-alpha)*b+a*gamma)=
      a^2*(alpha^2-alpha)*(41*P3-326*S3) := by
  let c11 := P2-2*S2
  let c21 := (P3-2*S3)/2
  have h11 : 41*c11=81*S2 := by
    dsimp [c11]
    linear_combination hq
  have h21 : 2*c21=P3-2*S3 := by dsimp [c21]; ring
  have hquad : S2*(1+alpha^2)+c11*alpha=0 := by
    linear_combination (S2/41)*hf+(alpha/41)*h11
  have h : a*((c11+2*S2*alpha)*((alpha^2-alpha)*b+a*gamma)+
      2*a^2*(S3*(1+alpha^3)+c21*alpha*(1+alpha)))=0 := by
    dsimp [c11,c21] at hquad ⊢
    unfold A2 B2 C3 D3 at hc
    linear_combination hc-2*a*b*hquad
  exact actualSliceTangent alpha a b gamma P3 S2 S3 c11 c21
    hf h11 h21 ((mul_eq_zero.mp h).resolve_left ha)

end
end Integration.Paper9SymmetricTauJet
