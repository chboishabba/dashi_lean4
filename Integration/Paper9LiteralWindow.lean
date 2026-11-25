import Integration.Paper9DiskGerm

/-! SOURCE-WRITTEN, UNCOMPILED. The original raw integer prefix
and all-index signed contraction give nested adjacent intervals.
Consume the actual period limit; no new real or convergence proof.
The Agda-to-Lean exact rational reflection remains separate. -/
namespace Integration.Paper9LiteralWindow
open Filter
open scoped Topology
open Integration.Paper9LiteralFactorialPrefix

def rho (n : ℕ) : ℚ :=
  -(leaf (n+1))*(weight (n+1):ℚ)/(weight n:ℚ)

theorem rhoFormula (n : ℕ) : rho n =
    (24*(2*(n:ℚ)+1)*(6*(n:ℚ)+1)*(6*(n:ℚ)+5)*
      (13591409+545140134*((n:ℚ)+1))) /
    ((640320:ℚ)^3*((n:ℚ)+1)^3*(13591409+545140134*(n:ℚ))) := by
  unfold rho leaf leafP leafQ weight
  push_cast
  ring

-- Same positive weighted gap as the original native positive-gap owner.
-- The expanded polynomial has positive coefficients at every n>=0.
theorem rhoBounds (n : ℕ) : 0≤rho n ∧ rho n<1/(2:ℚ)^41 := by
  rw [rhoFormula]
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).2
    let x : ℚ := n
    have hx : 0≤x := by positivity
    have hg : 0 <
      (640320:ℚ)^3*(x+1)^3*(13591409+545140134*x)-
        2^41*24*(2*x+1)*(6*x+1)*(6*x+5)*(13591409+545140134*(x+1)) := by
      calc
        _ = 141048195668958693853495296*x^4+
            427696936518221473282523136*x^3+
            435555656263180381923311616*x^2+
            152324142589183949932855296*x+
            3420813714202353688903680 := by ring
        _ > 0 := by positivity
    change _ < _
    nlinarith [hg]

theorem rhoLeOne (n : ℕ) : rho n≤1 :=
  (rhoBounds n).2.le.trans (by norm_num)

theorem adjacentConvex (n : ℕ) :
    sum (n+2)=rho n*sum n+(1-rho n)*sum (n+1) := by
  have h0 := sumStep n
  have h1 := sumStep (n+1)
  rw [productStep (n+1)] at h1
  have hw : (weight n:ℚ)≠0 := by unfold weight; push_cast; positivity
  unfold rho
  field_simp [hw]
  linear_combination (weight n:ℚ)*h1+
    (leaf (n+1)*(weight (n+1):ℚ))*h0

def lo (n : ℕ) : ℚ := min (sum n) (sum (n+1))
def hi (n : ℕ) : ℚ := max (sum n) (sum (n+1))

theorem nextInside (n : ℕ) : lo n≤sum (n+2) ∧ sum (n+2)≤hi n := by
  have h0 := (rhoBounds n).1
  have h1 : 0≤1-rho n := sub_nonneg.mpr (rhoLeOne n)
  rw [adjacentConvex]
  constructor
  · have hl := mul_le_mul_of_nonneg_left (min_le_left (sum n) (sum (n+1))) h0
    have hr := mul_le_mul_of_nonneg_left (min_le_right (sum n) (sum (n+1))) h1
    change min (sum n) (sum (n+1))≤_
    linarith
  · have hl := mul_le_mul_of_nonneg_left (le_max_left (sum n) (sum (n+1))) h0
    have hr := mul_le_mul_of_nonneg_left (le_max_right (sum n) (sum (n+1))) h1
    change _≤max (sum n) (sum (n+1))
    linarith

theorem nested (n : ℕ) : lo n≤lo (n+1) ∧ hi (n+1)≤hi n := by
  obtain ⟨hl,hh⟩ := nextInside n
  exact ⟨le_min (min_le_right _ _) hl,max_le (le_max_right _ _) hh⟩

theorem nestedAdd (n j : ℕ) :
    lo n≤lo (n+j) ∧ hi (n+j)≤hi n := by
  induction j with
  | zero => simp
  | succ j ih =>
    exact ⟨ih.1.trans (nested (n+j)).1,(nested (n+j)).2.trans ih.2⟩

theorem laterInside (n m : ℕ) (h : n≤m) :
    lo n≤sum m ∧ sum m≤hi n := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(nestedAdd n j).1.trans (min_le_left _ _),
    (le_max_left _ _).trans (nestedAdd n j).2⟩

theorem loPositive (n : ℕ) (hn : 1≤n) : 0<lo n := by
  have h : 0<lo 1 := by norm_num [lo,sum,prefix,leafP,leafQ,weight]
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact h.trans_le (nestedAdd 1 j).1

-- Close each fixed interval against the actual analytic limit. The
-- cutoff is arbitrary and no uniform choice of a limiting index is used.
theorem limitInside (v : ℝ)
    (h : Tendsto (fun N => (sum N:ℂ)) atTop (𝓝 (v:ℂ))) (n : ℕ) :
    (lo n:ℝ)≤v ∧ v≤(hi n:ℝ) := by
  have ht : Tendsto (fun N => (sum N:ℝ)) atTop (𝓝 v) := by
    simpa using (Complex.continuous_re.continuousAt.tendsto.comp h)
  constructor
  · apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with m hm
    exact_mod_cast (laterInside n m hm).1
  · apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with m hm
    exact_mod_cast (laterInside n m hm).2

-- Literal endpoint rational values: the source sorted positive pair
-- and the two consecutive integer square-root numerators.
def low (n r scale : ℕ) : ℚ := (426880*r:ℚ)/(scale:ℚ)/hi n
def high (n r scale : ℕ) : ℚ := (426880*(r+1):ℚ)/(scale:ℚ)/lo n

theorem rootBracket (r scale : ℕ) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2≤(r+1)^2) :
    (r:ℝ)/(scale:ℝ)≤Real.sqrt 10005 ∧
      Real.sqrt 10005≤((r+1:ℕ):ℝ)/(scale:ℝ) := by
  have hs' : 0<(scale:ℝ) := by exact_mod_cast hs
  have hl' : (r:ℝ)^2≤10005*(scale:ℝ)^2 := by exact_mod_cast hl
  have hu' : 10005*(scale:ℝ)^2≤((r:ℝ)+1)^2 := by exact_mod_cast hu
  have he : (Real.sqrt 10005*(scale:ℝ))^2=10005*(scale:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num)]
  have hn : 0≤Real.sqrt 10005*(scale:ℝ) := by positivity
  constructor
  · apply (div_le_iff₀ hs').2
    by_contra! hh
    have hp := mul_pos (sub_pos.mpr hh)
      (show 0<(r:ℝ)+Real.sqrt 10005*(scale:ℝ) by linarith)
    nlinarith
  · apply (le_div_iff₀ hs').2
    push_cast
    by_contra! hh
    have hp := mul_pos (sub_pos.mpr hh)
      (show 0<Real.sqrt 10005*(scale:ℝ)+((r:ℝ)+1) by positivity)
    nlinarith

theorem actualPiInside
    (h : Tendsto (fun N => (sum N:ℂ)) atTop
      (𝓝 ((426880*Real.sqrt 10005/Real.pi:ℝ):ℂ)))
    (n r scale : ℕ) (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2≤(r+1)^2) :
    (low n r scale:ℝ)≤Real.pi ∧ Real.pi≤(high n r scale:ℝ) := by
  obtain ⟨hlo,hhi⟩ := limitInside _ h n
  obtain ⟨hrootlo,hroothi⟩ := rootBracket r scale hs hl hu
  have hp := Real.pi_pos
  have hL : 0<(lo n:ℝ) := by exact_mod_cast loPositive n hn
  have hU : 0<(hi n:ℝ) := hL.trans_le (by exact_mod_cast
    (show lo n≤hi n from (min_le_left _ _).trans (le_max_left _ _)))
  have hlo' := (le_div_iff₀ hp).1 hlo
  have hhi' := (div_le_iff₀ hp).1 hhi
  unfold low high
  push_cast
  constructor
  · apply (div_le_iff₀ hU).2
    calc
      _ = 426880*((r:ℝ)/(scale:ℝ)) := by ring
      _ ≤ 426880*Real.sqrt 10005 := by gcongr
      _ ≤ _ := by linarith
  · apply (le_div_iff₀ hL).2
    calc
      Real.pi*(lo n:ℝ) ≤ 426880*Real.sqrt 10005 := by linarith
      _ ≤ 426880*(((r:ℝ)+1)/(scale:ℝ)) := by gcongr
      _ = _ := by ring

-- Rational cross, not a real-valued assertion in the conclusion.
-- The Machin bound is the existing source stage/radius producer;
-- the actual cross-prover reflection into Q^u remains to be built.
theorem rationalCross
    (h : Tendsto (fun N => (sum N:ℂ)) atTop
      (𝓝 ((426880*Real.sqrt 10005/Real.pi:ℝ):ℂ)))
    (n r scale : ℕ) (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2≤(r+1)^2)
    (m e : ℚ) (hm : |Real.pi-(m:ℝ)|≤(e:ℝ)) :
    low n r scale≤m+e ∧ m≤high n r scale+e := by
  obtain ⟨hlo,hhi⟩ := actualPiInside h n r scale hn hs hl hu
  obtain ⟨h1,h2⟩ := abs_le.mp hm
  constructor
  · exact_mod_cast (show (low n r scale:ℝ)≤(m:ℝ)+(e:ℝ) by linarith)
  · exact_mod_cast (show (m:ℝ)≤(high n r scale:ℝ)+(e:ℝ) by linarith)

end Integration.Paper9LiteralWindow
