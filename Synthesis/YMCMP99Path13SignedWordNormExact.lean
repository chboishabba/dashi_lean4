import Synthesis.YMSelectedPath13InverseEnclosureExact
import Mathlib.Tactic

/-!
Actual CMP98 Eq119/120 ordered Path13 word differential.
Source: check_ym_path13_full_mixed_jet.py and
check_ym_path13_full_q_matrix.py (walkword/deposit).
Each factor is an adjoint operator on a Lie coordinate, with signed
tangent at a negative bond inserted after that factor. All estimates
are in a submultiplicative operator norm, not an entrywise norm.
-/
namespace CMP99Pivot.Path13
noncomputable section
variable {R : Type*} [NormedRing R] [NormOneClass R]

structure BondVariation (R : Type*) where
  adj : R
  negative : Bool
  tangent : R

def flatTangent (b : BondVariation R) : R :=
  if b.negative then -b.tangent else b.tangent

def signedTangent (b : BondVariation R) : R :=
  if b.negative then -(b.adj*b.tangent) else b.tangent

def pathAdj : List (BondVariation R) → R
  | [] => 1
  | b::bs => b.adj*pathAdj bs

def pathTangent : List (BondVariation R) → R
  | [] => 0
  | b::bs => signedTangent b+b.adj*pathTangent bs

def pathFlat : List (BondVariation R) → R
  | [] => 0
  | b::bs => flatTangent b+pathFlat bs

def BondBound (e : ℝ) (b : BondVariation R) : Prop :=
  ‖b.adj‖≤1 ∧ ‖b.adj-1‖≤2*e ∧ ‖b.tangent‖≤1

theorem norm_mul_change (A B B₀ : R) :
    ‖A*B-B₀‖≤‖A-1‖*‖B‖+‖B-B₀‖ := by
  have h : A*B-B₀=(A-1)*B+(B-B₀) := by noncomm_ring
  rw [h]
  exact (norm_add_le _ _).trans
    (add_le_add_right (norm_mul_le _ _) _)

theorem signedTangent_bound (e : ℝ) (b : BondVariation R)
    (hb : BondBound e b) :
    ‖signedTangent b‖≤1 ∧ ‖signedTangent b-flatTangent b‖≤2*e := by
  rcases hb with ⟨hA,hE,hT⟩
  have he : 0≤2*e := (norm_nonneg _).trans hE
  by_cases h : b.negative=true
  · simp only [signedTangent,flatTangent,h,if_true,norm_neg]
    have hd : -(b.adj*b.tangent)- -b.tangent =
        -((b.adj-1)*b.tangent) := by noncomm_ring
    rw [hd,norm_neg]
    exact ⟨(norm_mul_le _ _).trans (by nlinarith [norm_nonneg b.adj,norm_nonneg b.tangent]),
      (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (b.adj-1),norm_nonneg b.tangent])⟩
  · simp [signedTangent,flatTangent,h,hT,he]

/-- Actual concatenation rule. The flat differential is the signed
sum of the original bond variations, with no omitted negative links. -/
theorem pathAdj_append (p q : List (BondVariation R)) :
    pathAdj (p++q)=pathAdj p*pathAdj q := by
  induction p with
  | nil => simp [pathAdj]
  | cons b bs ih => simp [pathAdj,ih,mul_assoc]

theorem pathTangent_append (p q : List (BondVariation R)) :
    pathTangent (p++q)=pathTangent p+pathAdj p*pathTangent q := by
  induction p with
  | nil => simp [pathAdj,pathTangent]
  | cons b bs ih => simp [pathAdj,pathTangent,ih,mul_add,mul_assoc,add_assoc]

theorem path_word_bounds (e : ℝ) (he : 0≤e)
    (p : List (BondVariation R)) (hp : ∀ b∈p,BondBound e b) :
    ‖pathAdj p‖≤1 ∧ ‖pathAdj p-1‖≤2*(p.length:ℝ)*e ∧
    ‖pathTangent p‖≤p.length ∧
    ‖pathTangent p-pathFlat p‖≤2*(p.length:ℝ)^2*e := by
  induction p with
  | nil => simp [pathAdj,pathTangent,pathFlat]
  | cons b bs ih =>
    have hb := hp b (List.mem_cons_self)
    have hbs := ih (fun c hc=>hp c (List.mem_cons_of_mem _ hc))
    rcases hbs with ⟨hA,hAd,hT,hTd⟩
    rcases signedTangent_bound e b hb with ⟨hB,hBd⟩
    have hn : 0≤(bs.length:ℝ) := by positivity
    have hmul : ‖b.adj*pathAdj bs‖≤1 :=
      (norm_mul_le _ _).trans (by nlinarith [hb.1,hA,norm_nonneg b.adj,norm_nonneg (pathAdj bs)])
    have hdiff := norm_mul_change b.adj (pathAdj bs) 1
    have hTmul : ‖b.adj*pathTangent bs‖≤bs.length :=
      (norm_mul_le _ _).trans (by nlinarith [hb.1,hT,norm_nonneg b.adj,norm_nonneg (pathTangent bs)])
    have hTd' := norm_mul_change b.adj (pathTangent bs) (pathFlat bs)
    have hsum : signedTangent b+b.adj*pathTangent bs-
        (flatTangent b+pathFlat bs) =
        (signedTangent b-flatTangent b)+(b.adj*pathTangent bs-pathFlat bs) := by abel
    simp only [pathAdj,pathTangent,pathFlat,List.length_cons,Nat.cast_succ]
    refine ⟨hmul,?_,?_,?_⟩
    · calc
        _ ≤ ‖b.adj-1‖*‖pathAdj bs‖+‖pathAdj bs-1‖ := hdiff
        _ ≤ 2*e+2*(bs.length:ℝ)*e := by
          gcongr
          · exact hb.2.1
          · exact hA
        _ = _ := by ring
    · exact (norm_add_le _ _).trans (by linarith [hB,hTmul])
    · rw [hsum]
      calc
        _ ≤ ‖signedTangent b-flatTangent b‖+
            ‖b.adj*pathTangent bs-pathFlat bs‖ := norm_add_le _ _
        _ ≤ 2*e+(2*e*(bs.length:ℝ)+2*(bs.length:ℝ)^2*e) := by
          have h := mul_le_mul hb.2.1 hT (norm_nonneg _) (by positivity : 0≤2*e)
          linarith
        _ ≤ 2*((bs.length:ℝ)+1)^2*e := by
          nlinarith [mul_nonneg hn he]

/-- Ordered source paths have at most 24 signed links; M and P each
add exactly a 13-link coarse segment, hence 37. The relative word
has at most 74. Specialization of the actual length estimate. -/
theorem path37_bounds (e : ℝ) (he : 0≤e)
    (p : List (BondVariation R)) (hp : ∀ b∈p,BondBound e b)
    (hlen : p.length≤37) :
    ‖pathAdj p‖≤1 ∧ ‖pathAdj p-1‖≤74*e ∧
    ‖pathTangent p‖≤37 ∧ ‖pathTangent p-pathFlat p‖≤2738*e := by
  have h := path_word_bounds e he p hp
  have hl : (p.length:ℝ)≤37 := by exact_mod_cast hlen
  refine ⟨h.1,?_,h.2.2.1.trans hl,?_⟩
  · exact h.2.1.trans (by gcongr <;> norm_num)
  · have hs : (p.length:ℝ)^2≤37^2 := by gcongr
    exact h.2.2.2.trans (by gcongr <;> norm_num)

end
end CMP99Pivot.Path13
