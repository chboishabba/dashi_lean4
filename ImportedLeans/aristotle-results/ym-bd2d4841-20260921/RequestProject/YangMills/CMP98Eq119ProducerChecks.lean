/-
# The Eq. (119) producer computes the expected classical value

`CMP98Eq119Producer` builds the one-step averaging derivative from the lattice
data alone.  A construction of that kind is only worth anything if it can be
evaluated, so this file evaluates it in the one case where the answer is known
independently: a flat background together with a *constant covariantly signed*
perturbation one-form `A(x, s) = ±v`.

Along a contour `Γ(p) = leg(p) ⌢ c ⌢ leg(p)^{-1}` the two legs cancel exactly
(orientation reversal negates the transported form), so the transported
one-form collapses to the contribution of the coarse bond alone, which has the
canonical length `13`.  Hence

    eq119Physical (flat link) (constant form v) c μ true = 13 • v ,

which is `eq119Physical_flat_const`.  In particular the operator is not
identically zero (`eq119Physical_flat_const_ne_zero`), the small-field
hypotheses it consumes are satisfiable (`flat_PhysicalSmallField`), and the
`13` really is the coarse-bond length rather than a normalisation artefact.
-/
import RequestProject.YangMills.CMP98Eq119Producer
import RequestProject.YangMills.CMP98Eq119Checks

namespace YangMills.CMP98Eq119

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Nontrivial A]
variable {N : ℕ}

/-! ## 1. The transported one-form at a flat background -/

omit [CompleteSpace A] [Nontrivial A] in
/-- At a flat background the transport is trivial, so `R₀A` is just the sum of
the one-form over the steps of the contour. -/
theorem rzero_flat_sum (A0 : Step 4 → A) (x : PSite 4 N) (w : List (Step 4)) :
    rzero (fun _ _ => (1 : Aˣ)) adjHom (fun _ s => A0 s) x w = (w.map A0).sum := by
  induction w generalizing x with
  | nil => simp
  | cons s ss ih => simp [rzero_cons, ih]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [Nontrivial A] in
theorem sum_map_revWord (A0 : Step 4 → A) (hA0 : ∀ s, A0 (revStep s) = -A0 s)
    (w : List (Step 4)) : ((revWord w).map A0).sum = -(w.map A0).sum := by
  induction w with
  | nil => simp
  | cons s ss ih =>
      rw [revWord_cons, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hA0 s]
      abel

omit [NormedAlgebra ℝ A] [CompleteSpace A] [Nontrivial A] in
theorem sum_map_axisSegment (A0 : Step 4 → A) (s : Step 4) (n : ℕ) :
    ((axisSegment s n).map A0).sum = n • A0 s := by
  simp [axisSegment, List.map_replicate, List.sum_replicate]

omit [CompleteSpace A] [Nontrivial A] in
/-- The two legs of the averaging contour cancel: only the coarse bond
survives. -/
theorem rzero_flat_physicalContour (A0 : Step 4 → A) (hA0 : ∀ s, A0 (revStep s) = -A0 s)
    (x : PSite 4 N) (μ : Fin 4) (o : Bool) (p : BlockOffset) :
    rzero (fun _ _ => (1 : Aˣ)) adjHom (fun _ s => A0 s) x (physicalContour μ o p)
      = (13 : ℕ) • A0 (μ, o) := by
  rw [rzero_flat_sum, physicalContour, eq119Contour]
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append,
    sum_map_revWord A0 hA0, coarseBond, sum_map_axisSegment]
  abel

/-! ## 2. The constant covariantly signed one-form -/

/-- The constant one-form with the covariant sign convention: `+v` on forward
steps, `−v` on backward steps. -/
def constForm (v : A) (s : Step 4) : A := if s.2 then v else -v

omit [NormedAlgebra ℝ A] [CompleteSpace A] [Nontrivial A] in
theorem constForm_revStep (v : A) (s : Step 4) :
    constForm v (revStep s) = -constForm v s := by
  obtain ⟨a, b⟩ := s
  cases b <;> simp [constForm, revStep]

omit [CompleteSpace A] [Nontrivial A] in
/-- It is a genuine covariantly signed one-form for the flat link field, so
`rzero_revWord` applies to it. -/
theorem constForm_covariant (v : A) :
    CovariantForm (V := A) (fun _ _ => (1 : Aˣ)) adjHom (fun (_ : PSite 4 N) s => constForm v s) := by
  intro x s
  simp [constForm_revStep]

/-! ## 3. The producer at the flat background -/

omit [Nontrivial A] in
theorem physicalYAt_flat (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) (p : BlockOffset) :
    physicalYAt (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o p = 0 := by
  simp [physicalYAt, physicalLog, relativeHolonomy_flat, expLog_one]

omit [CompleteSpace A] [Nontrivial A] in
@[simp] theorem adOp_zero : adOp (0 : A) = 0 := by
  ext z; simp

theorem physicalJMinus_flat (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) (p : BlockOffset) :
    physicalJMinus (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o p = 1 := by
  rw [physicalJMinus, physicalYAt_flat, adOp_zero, balabanG_zero, Ring.inverse_one]

/-- **The producer evaluates to the coarse-bond integral.**  At a flat
background, the Eq. (119) one-step averaging derivative of the constant
covariantly signed one-form `±v` is exactly `13 • v`, the canonical coarse-bond
length times the field. -/
theorem eq119Physical_flat_const (v : A) (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) :
    eq119Physical (fun _ _ => (1 : Aˣ)) (fun (_ : PSite 4 N) s => constForm v s) cMinus μ o
      = (13 : ℕ) • constForm v (μ, o) := by
  have hY : blockAverage (physicalYAt (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o) = 0 := by
    have : physicalYAt (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o = fun _ => (0 : A) := by
      funext p; exact physicalYAt_flat cMinus μ o p
    rw [this, blockAverage_const]
  have hsummand : ∀ p : BlockOffset,
      eq119Summand (fun _ _ => (1 : Aˣ)) (fun (_ : PSite 4 N) s => constForm v s)
        (physicalYAt (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o)
        (physicalJMinus (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o)
        legWord (coarseBond μ o) cMinus p = (13 : ℕ) • constForm v (μ, o) := by
    intro p
    rw [eq119Summand, hY, physicalJMinus_flat]
    have hcontour :
        rzero (fun _ _ => (1 : Aˣ)) adjHom (fun (_ : PSite 4 N) s => constForm v s) cMinus
            (eq119Contour legWord (coarseBond μ o) p)
          = (13 : ℕ) • constForm v (μ, o) :=
      rzero_flat_physicalContour _ (constForm_revStep v) cMinus μ o p
    rw [hcontour]
    simp
  rw [eq119Physical, eq119]
  have : eq119Summand (fun _ _ => (1 : Aˣ)) (fun (_ : PSite 4 N) s => constForm v s)
      (physicalYAt (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o)
      (physicalJMinus (A := A) (fun _ _ => (1 : Aˣ)) cMinus μ o) legWord (coarseBond μ o) cMinus
      = fun _ => (13 : ℕ) • constForm v (μ, o) := funext hsummand
  rw [this, blockAverage_const]

/-- Consequently the producer is not the zero operator. -/
theorem eq119Physical_flat_const_ne_zero (v : A) (hv : v ≠ 0) (cMinus : PSite 4 N)
    (μ : Fin 4) :
    eq119Physical (fun _ _ => (1 : Aˣ)) (fun (_ : PSite 4 N) s => constForm v s)
      cMinus μ true ≠ 0 := by
  rw [eq119Physical_flat_const]
  simp only [constForm, if_pos]
  intro h
  have h13 : ((13 : ℕ) : ℝ) • v = 0 := by
    rwa [Nat.cast_smul_eq_nsmul ℝ]
  rcases smul_eq_zero.1 h13 with h0 | h0
  · norm_num at h0
  · exact hv h0

omit [Nontrivial A] in
/-- The small-field hypothesis of the producer is satisfiable: the flat link
field meets it at every radius. -/
theorem flat_PhysicalSmallField {ε : ℝ} (hε : 0 < ε) (cMinus : PSite 4 N) (μ : Fin 4)
    (o : Bool) : PhysicalSmallField (A := A) ε (fun _ _ => (1 : Aˣ)) cMinus μ o := by
  constructor
  · intro p
    simpa [relativeHolonomy_flat] using hε
  · intro p
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [physicalYAt_flat, norm_zero]
    linarith

/-! ## 4. Axiom audit -/

#print axioms rzero_flat_physicalContour
#print axioms eq119Physical_flat_const
#print axioms eq119Physical_flat_const_ne_zero
#print axioms flat_PhysicalSmallField
#print axioms eq119Physical_from_lattice_data

end YangMills.CMP98Eq119
