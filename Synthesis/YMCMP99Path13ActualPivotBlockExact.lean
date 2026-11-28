import Synthesis.YMCMP99PivotRealCalculusExact

/-!
CMP98/99 selected Path13 flat averaging source. The original executable
check_ym_path13_full_q_matrix.py owns the quaternion-path Q jets and
reports the origin pivot I/13^4. Construct the actual block selection
and its inverse, rather than replacing the twelve Lie/bond coordinates
by an arbitrary scalar. The nonflat Q(s) and uniform CMP102 enclosure
remain source obligations.
-/
namespace CMP99Pivot.Path13
open Matrix
open scoped BigOperators
noncomputable section

abbrev Row := Fin 4 × Fin 3
abbrev Site := Fin (13^4)
abbrev Fine := Site × Row

def originQ : Matrix Row Fine ℝ :=
  fun r b => if r=b.2 then 1/(13^4:ℝ) else 0

def pivot (Q : Matrix Row Fine ℝ) : Matrix Row Row ℝ :=
  fun r c => Q r (0,c)

def remaining (Q : Matrix Row Fine ℝ) :
    Matrix Row ({s : Site // s≠0} × Row) ℝ :=
  fun r b => Q r (b.1.1,b.2)

theorem originPivot :
    pivot originQ = (1/(13^4:ℝ)) • (1 : Matrix Row Row ℝ) := by
  ext i j
  by_cases h : i=j <;> simp [pivot,originQ,Matrix.one_apply,h]

def originPivotInv : Matrix Row Row ℝ := (13^4:ℝ) • 1

theorem originPivotInverse :
    originPivotInv * pivot originQ=1 ∧ pivot originQ * originPivotInv=1 := by
  rw [originPivot]
  unfold originPivotInv
  constructor <;> simp [Matrix.smul_mul,Matrix.mul_smul,smul_smul] <;> norm_num

/-- The free/pivot decomposition of the exact source is a block map
Q_p c + Q_f b, with no independent eliminated coordinates. -/
def constraint (P : Matrix Row Row ℝ) (B : Matrix Row ({s : Site // s≠0} × Row) ℝ)
    (c : Matrix Row (Fin 1) ℝ) (b : Matrix ({s : Site // s≠0} × Row) (Fin 1) ℝ) :=
  P*c+B*b

def eliminated (G : Matrix Row Row ℝ) (B : Matrix Row ({s : Site // s≠0} × Row) ℝ)
    (b : Matrix ({s : Site // s≠0} × Row) (Fin 1) ℝ) := -(G*(B*b))

theorem constraint_bidi (P G : Matrix Row Row ℝ)
    (B : Matrix Row ({s : Site // s≠0} × Row) ℝ)
    (c : Matrix Row (Fin 1) ℝ) (b : Matrix ({s : Site // s≠0} × Row) (Fin 1) ℝ)
    (hl : G*P=1) (hr : P*G=1) :
    constraint P B c b=0 ↔ c=eliminated G B b := by
  constructor
  · intro h
    unfold constraint at h
    have hh := congrArg (fun Z : Matrix Row (Fin 1) ℝ => G*Z) h
    rw [Matrix.mul_add,← Matrix.mul_assoc,hl,one_mul,mul_zero] at hh
    exact eq_neg_of_add_eq_zero_left hh
  · intro h
    rw [h]
    unfold constraint eliminated
    rw [mul_neg,← Matrix.mul_assoc,hr,one_mul,neg_add_cancel]

theorem originConstraint_bidi
    (c : Matrix Row (Fin 1) ℝ) (b : Matrix ({s : Site // s≠0} × Row) (Fin 1) ℝ) :
    constraint (pivot originQ) (remaining originQ) c b=0 ↔
      c=eliminated originPivotInv (remaining originQ) b :=
  constraint_bidi _ _ _ _ _ originPivotInverse.1 originPivotInverse.2

/-- Noncommutative signed two-point defect of the actual selected
block solve; note both pivot and free-block changes. -/
theorem block_defect (P₀ P₁ G₀ G₁ : Matrix Row Row ℝ)
    (B₀ B₁ : Matrix Row ({s : Site // s≠0} × Row) ℝ)
    (b : Matrix ({s : Site // s≠0} × Row) (Fin 1) ℝ)
    (hl : G₁*P₁=1) (hr : P₀*G₀=1) :
    eliminated G₁ B₁ b-eliminated G₀ B₀ b =
      -(G₁*((B₁-B₀)*b)) +
      G₁*((P₁-P₀)*(G₀*(B₀*b))) := by
  have hInv : G₀-G₁=G₁*(P₁-P₀)*G₀ := by
    calc
      G₀-G₁=(G₁*P₁)*G₀-G₁*(P₀*G₀) := by rw [hl,hr,one_mul,mul_one]
      _=G₁*(P₁-P₀)*G₀ := by simp [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  unfold eliminated
  rw [← Matrix.mul_assoc G₁ (P₁-P₀),← Matrix.mul_assoc
      (G₁*(P₁-P₀)) G₀,← hInv]
  simp only [Matrix.sub_mul,Matrix.mul_sub,neg_sub]
  abel

end
end CMP99Pivot.Path13
