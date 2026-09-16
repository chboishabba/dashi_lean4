/-
# The generic noncommutative mixed-third product recursion

The object that enters the Row A1a Gaussian floor,

    W = D_background Δ_Wilson,

is **not** the first variation of the Wilson action.  `Δ_Wilson` is already the
second (Hessian) variation, so `W` is the *mixed third* variation:

    D S  →  D² S  →  D³ S = W.

Computing a mixed third variation of a product of noncommuting link variables
needs a Leibniz recursion that keeps the factor order.  This file supplies it,
and does not merely postulate the combinatorial formula: the recursion is
*derived* from ordinary one-parameter calculus.

## What is here

* `Jet3` : a three-direction jet of a matrix-valued background family — its
  value, its three first variations, its three mixed second variations and its
  mixed third variation.
* `jetMul` : the ordered eight-term Leibniz product of two jets.
* `JetCarrier` : a three-parameter matrix family together with the nested
  one-parameter derivative data exhibiting a jet.  This is the honest analytic
  content: no combinatorial formula is assumed, only iterated derivatives.
* `JetCarrier.hasMixedD3` : the carrier's mixed third derivative at the origin
  is `jet.d123`.
* **`JetCarrier.mul`** : the product of two carriers is a carrier whose jet is
  `jetMul`.  Every one of the eight components is *derived* by the
  noncommutative product rule; in particular the top component is the ordered
  eight-term sum.
* `JetCarrier.mul₄` and `mixedD3_plaquette` : the recursion iterates, so the
  mixed third variation of an ordered product of four links — the shape of a
  Wilson plaquette — is computed by three nested applications.
* `jetMul_assoc` : the recursion does not depend on the bracketing.
* `first_variation_does_not_control_third` : a jet whose first variations all
  vanish while its mixed third variation does not.  This is the formal content
  of "`W` is the third variation, not the first".

Nothing here asserts the literal SU(N) link jets of the Wilson action; what is
proved is the recursion those jets are fed into.
-/
import RequestProject.YangMills.MatrixFamilyDerivative

namespace YangMills

open Matrix

variable {n : Type*} [Fintype n]

/-- A three-direction jet of a matrix-valued background family. -/
structure Jet3 (n : Type*) where
  /-- the value at the base point -/
  v : Matrix n n ℝ
  /-- first variation in direction 1 -/
  d1 : Matrix n n ℝ
  /-- first variation in direction 2 -/
  d2 : Matrix n n ℝ
  /-- first variation in direction 3 -/
  d3 : Matrix n n ℝ
  /-- mixed second variation in directions 1,2 -/
  d12 : Matrix n n ℝ
  /-- mixed second variation in directions 1,3 -/
  d13 : Matrix n n ℝ
  /-- mixed second variation in directions 2,3 -/
  d23 : Matrix n n ℝ
  /-- mixed third variation -/
  d123 : Matrix n n ℝ

namespace Jet3

/-- **The ordered eight-term Leibniz product of two jets.** -/
def jetMul (x y : Jet3 n) : Jet3 n where
  v := x.v * y.v
  d1 := x.d1 * y.v + x.v * y.d1
  d2 := x.d2 * y.v + x.v * y.d2
  d3 := x.d3 * y.v + x.v * y.d3
  d12 := x.d12 * y.v + x.d2 * y.d1 + x.d1 * y.d2 + x.v * y.d12
  d13 := x.d13 * y.v + x.d3 * y.d1 + x.d1 * y.d3 + x.v * y.d13
  d23 := x.d23 * y.v + x.d3 * y.d2 + x.d2 * y.d3 + x.v * y.d23
  d123 := x.d123 * y.v + x.d23 * y.d1 + x.d13 * y.d2 + x.d3 * y.d12
    + x.d12 * y.d3 + x.d2 * y.d13 + x.d1 * y.d23 + x.v * y.d123

/-- The recursion does not depend on the bracketing. -/
theorem jetMul_assoc [DecidableEq n] (x y z : Jet3 n) :
    jetMul (jetMul x y) z = jetMul x (jetMul y z) := by
  simp only [jetMul, Jet3.mk.injEq]
  refine ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring, by noncomm_ring,
    by noncomm_ring, by noncomm_ring, by noncomm_ring, by noncomm_ring⟩

end Jet3

/-- An affine matrix family has the obvious derivative. -/
theorem hasMatDerivAt_affine {m k : Type*} (M N : Matrix m k ℝ) (r0 : ℝ) :
    HasMatDerivAt (fun r => M + r • N) N r0 := by
  intro i j
  have hfun : (fun r => (M + r • N) i j) = fun r => M i j + r * N i j := by
    funext r; simp
  rw [hfun]
  simpa using ((hasDerivAt_mul_const (N i j)).const_add (M i j))

/-- The mixed third derivative at the origin, as three nested one-parameter
derivatives. -/
def HasMixedD3 (F : ℝ → ℝ → ℝ → Matrix n n ℝ) (W : Matrix n n ℝ) : Prop :=
  ∃ G : ℝ → ℝ → Matrix n n ℝ,
    (∀ s t, HasMatDerivAt (fun u => F s t u) (G s t) 0) ∧
    ∃ H : ℝ → Matrix n n ℝ,
      (∀ s, HasMatDerivAt (fun t => G s t) (H s) 0) ∧ HasMatDerivAt H W 0

/-- A three-parameter matrix family together with the nested one-parameter
derivative data that exhibits a three-direction jet. -/
structure JetCarrier (n : Type*) [Fintype n] where
  /-- the family -/
  F : ℝ → ℝ → ℝ → Matrix n n ℝ
  /-- the `u = 0` slice -/
  X0 : ℝ → ℝ → Matrix n n ℝ
  /-- the `u`-derivative slice -/
  X3 : ℝ → ℝ → Matrix n n ℝ
  /-- `t = 0` value of the `u = 0` slice -/
  a : ℝ → Matrix n n ℝ
  /-- `t`-derivative of the `u = 0` slice -/
  b : ℝ → Matrix n n ℝ
  /-- `t = 0` value of the `u`-derivative slice -/
  c : ℝ → Matrix n n ℝ
  /-- `t`-derivative of the `u`-derivative slice -/
  e : ℝ → Matrix n n ℝ
  /-- the jet exhibited -/
  jet : Jet3 n
  hF0 : ∀ s t, F s t 0 = X0 s t
  hFu : ∀ s t, HasMatDerivAt (fun u => F s t u) (X3 s t) 0
  hX0t0 : ∀ s, X0 s 0 = a s
  hX0t : ∀ s, HasMatDerivAt (fun t => X0 s t) (b s) 0
  hX3t0 : ∀ s, X3 s 0 = c s
  hX3t : ∀ s, HasMatDerivAt (fun t => X3 s t) (e s) 0
  ha0 : a 0 = jet.v
  has : HasMatDerivAt a jet.d1 0
  hb0 : b 0 = jet.d2
  hbs : HasMatDerivAt b jet.d12 0
  hc0 : c 0 = jet.d3
  hcs : HasMatDerivAt c jet.d13 0
  he0 : e 0 = jet.d23
  hes : HasMatDerivAt e jet.d123 0

namespace JetCarrier

variable {n : Type*} [Fintype n]

/-- **The carrier's mixed third derivative is the top jet component.** -/
theorem hasMixedD3 (K : JetCarrier n) : HasMixedD3 K.F K.jet.d123 :=
  ⟨K.X3, K.hFu, K.e, K.hX3t, K.hes⟩

/-- **The product of two carriers is a carrier, with jet the ordered Leibniz
product.**  Every component is derived by the noncommutative product rule. -/
def mul (K L : JetCarrier n) : JetCarrier n where
  F := fun s t u => K.F s t u * L.F s t u
  X0 := fun s t => K.X0 s t * L.X0 s t
  X3 := fun s t => K.X3 s t * L.X0 s t + K.X0 s t * L.X3 s t
  a := fun s => K.a s * L.a s
  b := fun s => K.b s * L.a s + K.a s * L.b s
  c := fun s => K.c s * L.a s + K.a s * L.c s
  e := fun s => K.e s * L.a s + K.c s * L.b s + (K.b s * L.c s + K.a s * L.e s)
  jet := Jet3.jetMul K.jet L.jet
  hF0 := by intro s t; rw [K.hF0, L.hF0]
  hFu := by
    intro s t
    have h := (K.hFu s t).mul (L.hFu s t)
    rw [K.hF0, L.hF0] at h
    exact h
  hX0t0 := by intro s; rw [K.hX0t0, L.hX0t0]
  hX0t := by
    intro s
    have h := (K.hX0t s).mul (L.hX0t s)
    rw [K.hX0t0, L.hX0t0] at h
    exact h
  hX3t0 := by intro s; rw [K.hX0t0, L.hX0t0, K.hX3t0, L.hX3t0]
  hX3t := by
    intro s
    have h := ((K.hX3t s).mul (L.hX0t s)).add ((K.hX0t s).mul (L.hX3t s))
    rw [K.hX0t0, L.hX0t0, K.hX3t0, L.hX3t0] at h
    exact h
  ha0 := by rw [K.ha0, L.ha0]; rfl
  has := by
    have h := K.has.mul L.has
    rw [K.ha0, L.ha0] at h
    exact h
  hb0 := by rw [K.hb0, K.ha0, L.hb0, L.ha0]; rfl
  hbs := by
    have h := (K.hbs.mul L.has).add (K.has.mul L.hbs)
    rw [K.ha0, L.ha0, K.hb0, L.hb0] at h
    have hval : K.jet.d12 * L.jet.v + K.jet.d2 * L.jet.d1
        + (K.jet.d1 * L.jet.d2 + K.jet.v * L.jet.d12)
        = (Jet3.jetMul K.jet L.jet).d12 := by
      simp only [Jet3.jetMul]; abel
    rw [← hval]
    exact h
  hc0 := by rw [K.hc0, K.ha0, L.hc0, L.ha0]; rfl
  hcs := by
    have h := (K.hcs.mul L.has).add (K.has.mul L.hcs)
    rw [K.ha0, L.ha0, K.hc0, L.hc0] at h
    have hval : K.jet.d13 * L.jet.v + K.jet.d3 * L.jet.d1
        + (K.jet.d1 * L.jet.d3 + K.jet.v * L.jet.d13)
        = (Jet3.jetMul K.jet L.jet).d13 := by
      simp only [Jet3.jetMul]; abel
    rw [← hval]
    exact h
  he0 := by rw [K.he0, K.ha0, K.hc0, K.hb0, L.he0, L.ha0, L.hc0, L.hb0]; simp [Jet3.jetMul]; abel
  hes := by
    have h := ((K.hes.mul L.has).add (K.hcs.mul L.hbs)).add
      ((K.hbs.mul L.hcs).add (K.has.mul L.hes))
    rw [K.ha0, L.ha0, K.hb0, L.hb0, K.hc0, L.hc0, K.he0, L.he0] at h
    have hval : K.jet.d123 * L.jet.v + K.jet.d23 * L.jet.d1
        + (K.jet.d13 * L.jet.d2 + K.jet.d3 * L.jet.d12)
        + (K.jet.d12 * L.jet.d3 + K.jet.d2 * L.jet.d13
          + (K.jet.d1 * L.jet.d23 + K.jet.v * L.jet.d123))
        = (Jet3.jetMul K.jet L.jet).d123 := by
      simp only [Jet3.jetMul]; abel
    rw [← hval]
    exact h

@[simp] theorem mul_F (K L : JetCarrier n) :
    (K.mul L).F = fun s t u => K.F s t u * L.F s t u := rfl

@[simp] theorem mul_jet (K L : JetCarrier n) :
    (K.mul L).jet = Jet3.jetMul K.jet L.jet := rfl

/-- The four-factor ordered product — the shape of a Wilson plaquette. -/
def mul₄ (K L M N : JetCarrier n) : JetCarrier n := ((K.mul L).mul M).mul N

/-- **The mixed third variation of an ordered product of four link families**
is computed by three nested applications of the recursion. -/
theorem mixedD3_plaquette (K L M N : JetCarrier n) :
    HasMixedD3 (fun s t u => K.F s t u * L.F s t u * M.F s t u * N.F s t u)
      (Jet3.jetMul (Jet3.jetMul (Jet3.jetMul K.jet L.jet) M.jet) N.jet).d123 :=
  (mul₄ K L M N).hasMixedD3

end JetCarrier

namespace Jet3

/-! ### Carriers exist: the multi-affine family of a jet -/

/-- The multi-affine family represented by a jet,
`F(s,t,u) = v + s d₁ + t d₂ + u d₃ + st d₁₂ + su d₁₃ + tu d₂₃ + stu d₁₂₃`. -/
def jetFun (x : Jet3 n) (s t u : ℝ) : Matrix n n ℝ :=
  x.v + s • x.d1 + t • x.d2 + u • x.d3 + (s * t) • x.d12 + (s * u) • x.d13
    + (t * u) • x.d23 + (s * t * u) • x.d123

/-- The `u = 0` slice of `jetFun`. -/
def sl0 (x : Jet3 n) (s t : ℝ) : Matrix n n ℝ :=
  x.v + s • x.d1 + t • x.d2 + (s * t) • x.d12

/-- The `u`-derivative slice of `jetFun`. -/
def sl3 (x : Jet3 n) (s t : ℝ) : Matrix n n ℝ :=
  x.d3 + s • x.d13 + t • x.d23 + (s * t) • x.d123

omit [Fintype n] in
theorem jetFun_eq_slices (x : Jet3 n) (s t u : ℝ) :
    x.jetFun s t u = x.sl0 s t + u • x.sl3 s t := by
  unfold jetFun sl0 sl3
  simp only [smul_add, smul_smul]
  module

omit [Fintype n] in
theorem sl0_eq (x : Jet3 n) (s t : ℝ) :
    x.sl0 s t = (x.v + s • x.d1) + t • (x.d2 + s • x.d12) := by
  unfold sl0
  simp only [smul_add, smul_smul]
  module

omit [Fintype n] in
theorem sl3_eq (x : Jet3 n) (s t : ℝ) :
    x.sl3 s t = (x.d3 + s • x.d13) + t • (x.d23 + s • x.d123) := by
  unfold sl3
  simp only [smul_add, smul_smul]
  module

/-- **Every jet is carried by its multi-affine family.**  So `JetCarrier` is
inhabited and the recursion is not vacuous. -/
def carrier (x : Jet3 n) : JetCarrier n where
  F := x.jetFun
  X0 := x.sl0
  X3 := x.sl3
  a := fun s => x.v + s • x.d1
  b := fun s => x.d2 + s • x.d12
  c := fun s => x.d3 + s • x.d13
  e := fun s => x.d23 + s • x.d123
  jet := x
  hF0 := by intro s t; rw [jetFun_eq_slices]; simp
  hFu := by
    intro s t
    have hfun : (fun u => x.jetFun s t u) = fun u => x.sl0 s t + u • x.sl3 s t := by
      funext u; exact jetFun_eq_slices x s t u
    rw [hfun]
    exact hasMatDerivAt_affine _ _ 0
  hX0t0 := by intro s; rw [sl0_eq]; simp
  hX0t := by
    intro s
    have hfun : (fun t => x.sl0 s t)
        = fun t => (x.v + s • x.d1) + t • (x.d2 + s • x.d12) := by
      funext t; exact sl0_eq x s t
    rw [hfun]
    exact hasMatDerivAt_affine _ _ 0
  hX3t0 := by intro s; rw [sl3_eq]; simp
  hX3t := by
    intro s
    have hfun : (fun t => x.sl3 s t)
        = fun t => (x.d3 + s • x.d13) + t • (x.d23 + s • x.d123) := by
      funext t; exact sl3_eq x s t
    rw [hfun]
    exact hasMatDerivAt_affine _ _ 0
  ha0 := by simp
  has := hasMatDerivAt_affine _ _ 0
  hb0 := by simp
  hbs := hasMatDerivAt_affine _ _ 0
  hc0 := by simp
  hcs := hasMatDerivAt_affine _ _ 0
  he0 := by simp
  hes := hasMatDerivAt_affine _ _ 0

/-- The mixed third derivative of a jet's own family is its top component. -/
theorem hasMixedD3_jetFun (x : Jet3 n) : HasMixedD3 x.jetFun x.d123 :=
  (carrier x).hasMixedD3

/-- **The recursion, on genuine multi-affine link families.**  The mixed third
derivative of the ordered product of four such families is the top component of
the four-fold ordered Leibniz product of their jets. -/
theorem hasMixedD3_jetFun_four (a b c d : Jet3 n) :
    HasMixedD3
      (fun s t u => a.jetFun s t u * b.jetFun s t u * c.jetFun s t u * d.jetFun s t u)
      (jetMul (jetMul (jetMul a b) c) d).d123 :=
  JetCarrier.mixedD3_plaquette (carrier a) (carrier b) (carrier c) (carrier d)

/-- **The first variation does not control the third.**  There is a jet whose
three first variations all vanish while its mixed third variation does not, and
one with a nonvanishing first variation and vanishing mixed third variation.  So
`W = D³S` is genuinely a different datum from `DS`. -/
theorem first_variation_does_not_control_third :
    (∃ x : Jet3 (Fin 1), x.d1 = 0 ∧ x.d2 = 0 ∧ x.d3 = 0 ∧ x.d123 ≠ 0) ∧
    (∃ x : Jet3 (Fin 1), x.d1 ≠ 0 ∧ x.d123 = 0) := by
  have hone : (1 : Matrix (Fin 1) (Fin 1) ℝ) ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  exact ⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 1⟩, rfl, rfl, rfl, hone⟩,
    ⟨⟨0, 1, 0, 0, 0, 0, 0, 0⟩, hone, rfl⟩⟩

end Jet3

end YangMills
