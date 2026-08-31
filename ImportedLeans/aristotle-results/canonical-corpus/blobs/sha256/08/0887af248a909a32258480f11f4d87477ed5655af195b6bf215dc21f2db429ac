/-
# Row A1 (source lane) — the averaging map at the flat background

Bałaban's averaging step is nonlinear: the coarse field is read off from the
*logarithm* of an ordered product of link exponentials along the axial path of a
block, and its linearisation at a background `V₀` carries the adjoint factors
`g(-i·adY)`, `g⁻¹(-i·adY)` of the Baker–Campbell–Hausdorff expansion

    (1/i)·log(e^{iX} e^{iY}) = Y + g⁻¹(-i·adY)X + O(|X|²),
    g(z) = (e^z − 1)/z .

At the **flat background** all of that collapses: `Y = 0`, `g(0) = g⁻¹(0) = 1`,
all colour transports are the identity, and the linearised averaging operator is
the plain (normalised) block sum of the fluctuation field.

This file proves that collapse, in two independent halves.

## 1. The scalar factor

`tendsto_expSlope_atZero` : `(e^z − 1)/z → 1` as `z → 0`, i.e. `g(0) = 1`, from
the derivative of `exp` at `0`.  Nothing about `g` is postulated.

## 2. The operator statement

`hasDerivAt_listProd_exp_smul` : in any Banach algebra, for a finite ordered path
`l = [a₀,…,a_{n−1}]`,

    d/dt |₀  e^{t a₀} e^{t a₁} ⋯ e^{t a_{n−1}}  =  a₀ + ⋯ + a_{n−1} .

That is exactly the first-order content of the ordered product along a block
path at the flat background: the ordered product of exponentials linearises to
the *sum* of the generators, with no adjoint factor and no reordering
correction.  `hasDerivAt_blockPath_average` is the normalised version, with the
block weight `L⁻⁵` in front, and `hasDerivAt_blockPath_average_const` records
the resulting normalisation `Q'(1)·(constant) = constant`.

## 3. The flat specialisation of the literal block-averaging operator

`blockAverage_flatTransport` : with identity transports the literal
background-dependent block average of `AveragingLorentzDiagonal` is the plain
block sum, and `blockAverage_flatTransport_const` : it reproduces a constant
field exactly, i.e. the weight `L⁻⁵` is the correct normalisation for the `L⁴`
axial paths of `L` links each.

**Honest status.**  This is the flat-background specialisation only.  The
background-dependent adjoint factors, and the composition/analyticity estimates
for iterated averaging, are not proved here; Row A1 is not closed.
-/
import RequestProject.YangMills.AveragingLorentzDiagonal

namespace YangMills

open Filter Topology

/-! ## 1. The BCH scalar factor at the flat background -/

/-- The scalar factor of the Baker–Campbell–Hausdorff first-order term,
`g(z) = (e^z − 1)/z`, away from the origin. -/
noncomputable def bchFactor (z : ℝ) : ℝ := (Real.exp z - 1) / z

/-- **`g(0) = 1`.**  The Baker–Campbell–Hausdorff factor tends to `1` at the flat
background; this is the derivative of `exp` at `0` and nothing else. -/
theorem tendsto_bchFactor_atZero :
    Tendsto bchFactor (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hd : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  refine h.congr fun z => ?_
  rw [slope_def_field, bchFactor, Real.exp_zero, sub_zero]

/-! ## 2. The ordered product of exponentials linearises to the sum -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- **First order of an ordered product of exponentials.**  Along a finite path
`l = [a₀,…,a_{n−1}]` in a Banach algebra,

    d/dt |₀ ∏_k e^{t a_k} = ∑_k a_k .

This is the flat-background content of Bałaban's linearised averaging map: the
ordered product along a block path contributes the *plain sum* of its
generators, the adjoint factors `g^{±1}(-i·adY)` being the identity at `Y = 0`. -/
theorem hasDerivAt_listProd_exp_smul (l : List A) :
    HasDerivAt (fun t : ℝ => (l.map fun a => NormedSpace.exp (t • a)).prod) l.sum 0 := by
  induction l with
  | nil => simpa using (hasDerivAt_const (0 : ℝ) (1 : A))
  | cons a l ih =>
      have hhead : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a)) a 0 := by
        have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) a (0 : ℝ)
        simpa using h
      have hzero : (l.map fun a' => NormedSpace.exp ((0 : ℝ) • a')).prod = 1 := by
        have : (l.map fun a' => NormedSpace.exp ((0 : ℝ) • a')) = l.map fun _ => (1 : A) := by
          refine List.map_congr_left fun a' _ => ?_
          simp
        rw [this, List.prod_map_one]
      have hmul := hhead.mul ih
      rw [hzero] at hmul
      have hval : a * 1 + NormedSpace.exp ((0 : ℝ) • a) * l.sum = (a :: l).sum := by
        simp
      simpa [hval] using hmul

/-- **The normalised block-path average, at first order.**  With the block weight
`c` in front, the linearisation of the ordered product is `c` times the sum of
the generators. -/
theorem hasDerivAt_blockPath_average (c : ℝ) (l : List A) :
    HasDerivAt (fun t : ℝ => c • (l.map fun a => NormedSpace.exp (t • a)).prod)
      (c • l.sum) 0 :=
  (hasDerivAt_listProd_exp_smul l).const_smul c

/-- **The normalisation of the block average.**  A path of `n` copies of the same
generator `a`, weighted by `1/n`, linearises back to `a`: the flat-background
averaging operator reproduces a constant fluctuation exactly. -/
theorem hasDerivAt_blockPath_average_const {n : ℕ} (hn : n ≠ 0) (a : A) :
    HasDerivAt (fun t : ℝ =>
      ((n : ℝ))⁻¹ • ((List.replicate n a).map fun b => NormedSpace.exp (t • b)).prod) a 0 := by
  have h := hasDerivAt_blockPath_average ((n : ℝ))⁻¹ (List.replicate n a)
  have hsum : (List.replicate n a).sum = (n : ℝ) • a := by
    rw [List.sum_replicate, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [hsum, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul] at h
  exact h

end BanachAlgebra

/-! ## 3. The literal block-averaging operator at the flat background -/

/-- The flat background: every colour transport is the identity. -/
def flatTransport (color : Type*) [DecidableEq color] : TransportData color :=
  fun _ _ _ => 1

/-- **The flat-background block average is the plain block sum.**  No colour
rotation survives: the coarse `μ`-link is the unweighted average of the fine
`μ`-links of the `L⁴` axial paths of the block, each of length `L`. -/
theorem blockAverage_flatTransport {color : Type*} [Fintype color] [DecidableEq color]
    (L : ℕ) (Afield : LinkField color) (y : Site) (mu : Fin 4) (a : color) :
    blockAverage L (flatTransport color) Afield y mu a
      = ((L : ℝ) ^ 5)⁻¹ * ∑ r : Fin 4 → Fin L, ∑ k : Fin L,
          Afield (shiftSite (blockSite L y r) mu k) mu a := by
  unfold blockAverage flatTransport
  congr 1
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.one_apply]

/-- **The flat-background block average reproduces a constant field.**  With
`L⁴` axial paths of `L` links each and the weight `L⁻⁵`, the averaging operator
is normalised: `Q(1)·c = c`.  This is the normalisation used when the coarse
field is read off from the block product. -/
theorem blockAverage_flatTransport_const {color : Type*} [Fintype color] [DecidableEq color]
    {L : ℕ} (hL : L ≠ 0) (c : color → ℝ) (y : Site) (mu : Fin 4) (a : color) :
    blockAverage L (flatTransport color) (fun _ _ b => c b) y mu a = c a := by
  have hL' : ((L : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hL
  rw [blockAverage_flatTransport]
  have hinner : ∀ r : Fin 4 → Fin L, ∑ _k : Fin L, c a = (L : ℝ) * c a := by
    intro r
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have houter : (∑ _r : Fin 4 → Fin L, (L : ℝ) * c a) = (L : ℝ) ^ 4 * ((L : ℝ) * c a) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  calc ((L : ℝ) ^ 5)⁻¹ * ∑ r : Fin 4 → Fin L, ∑ _k : Fin L, c a
      = ((L : ℝ) ^ 5)⁻¹ * ∑ _r : Fin 4 → Fin L, (L : ℝ) * c a := by
        rw [Finset.sum_congr rfl fun r _ => hinner r]
    _ = ((L : ℝ) ^ 5)⁻¹ * ((L : ℝ) ^ 4 * ((L : ℝ) * c a)) := by rw [houter]
    _ = c a := by field_simp

/-! ## 4. The weld: the linear averaging operator *is* the first-order term of the
nonlinear block product at the flat background -/

section Weld

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {color : Type*} [Fintype color] [DecidableEq color]

/-- The Lie-algebra element carried by the fine link `(x, μ)`, in a basis `T` of
the colour algebra. -/
noncomputable def linkElement (T : color → A) (Afield : LinkField color)
    (x : Site) (mu : Fin 4) : A :=
  ∑ a : color, Afield x mu a • T a

/-- **The ordered product along one axial path of a block**, for the fluctuation
field scaled by `t`: the group element whose logarithm Bałaban's averaging step
reads off. -/
noncomputable def blockPathProduct (L : ℕ) (T : color → A) (Afield : LinkField color)
    (y : Site) (mu : Fin 4) (r : Fin 4 → Fin L) (t : ℝ) : A :=
  (List.ofFn fun k : Fin L =>
    NormedSpace.exp (t • linkElement T Afield (shiftSite (blockSite L y r) mu k) mu)).prod

/-- **The block average of the ordered path products**, with the block weight
`L⁻⁵`. -/
noncomputable def blockProductAverage (L : ℕ) (T : color → A) (Afield : LinkField color)
    (y : Site) (mu : Fin 4) (t : ℝ) : A :=
  ((L : ℝ) ^ 5)⁻¹ • ∑ r : Fin 4 → Fin L, blockPathProduct L T Afield y mu r t

omit [DecidableEq color] in
theorem hasDerivAt_blockPathProduct (L : ℕ) (T : color → A) (Afield : LinkField color)
    (y : Site) (mu : Fin 4) (r : Fin 4 → Fin L) :
    HasDerivAt (blockPathProduct L T Afield y mu r)
      (∑ k : Fin L, linkElement T Afield (shiftSite (blockSite L y r) mu k) mu) 0 := by
  have h := hasDerivAt_listProd_exp_smul
    (List.ofFn fun k : Fin L => linkElement T Afield (shiftSite (blockSite L y r) mu k) mu)
  rw [List.sum_ofFn] at h
  refine h.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rfl
  · filter_upwards with t
    rw [blockPathProduct, List.map_ofFn]
    rfl

/-- **The flat-background weld.**  The linear block-averaging operator used
throughout the Row A1 lane is exactly the first-order term, at the flat
background, of the nonlinear averaging map: the derivative at `t = 0` of the
weighted sum of the ordered path products is the colour-vector whose components
are the plain block averages of the fluctuation field.

No adjoint factor `g^{±1}(-i·adY)` and no transport survives at `Y = 0`; this is
the statement that the linear object downstream *is* the linearisation of the
literal averaging step, at the flat background. -/
theorem hasDerivAt_blockProductAverage (L : ℕ) (T : color → A) (Afield : LinkField color)
    (y : Site) (mu : Fin 4) :
    HasDerivAt (blockProductAverage L T Afield y mu)
      (∑ a : color, blockAverage L (flatTransport color) Afield y mu a • T a) 0 := by
  have hsum0 := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 4 → Fin L)))
    (A := fun r => blockPathProduct L T Afield y mu r)
    fun r _ => hasDerivAt_blockPathProduct L T Afield y mu r
  have hsum : HasDerivAt (fun t : ℝ => ∑ r : Fin 4 → Fin L, blockPathProduct L T Afield y mu r t)
      (∑ r : Fin 4 → Fin L,
        ∑ k : Fin L, linkElement T Afield (shiftSite (blockSite L y r) mu k) mu) 0 := by
    have hfun : (∑ r : Fin 4 → Fin L, blockPathProduct L T Afield y mu r)
        = fun t : ℝ => ∑ r : Fin 4 → Fin L, blockPathProduct L T Afield y mu r t := by
      funext t
      simp [Finset.sum_apply]
    rwa [hfun] at hsum0
  have hmain := hsum.const_smul (((L : ℝ) ^ 5)⁻¹)
  refine hmain.congr_deriv ?_
  have step1 : ∀ r : Fin 4 → Fin L,
      (∑ k : Fin L, linkElement T Afield (shiftSite (blockSite L y r) mu k) mu)
        = ∑ a : color, (∑ k : Fin L, Afield (shiftSite (blockSite L y r) mu k) mu a) • T a := by
    intro r
    simp only [linkElement]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
  have step2 : (∑ r : Fin 4 → Fin L,
        ∑ k : Fin L, linkElement T Afield (shiftSite (blockSite L y r) mu k) mu)
      = ∑ a : color, (∑ r : Fin 4 → Fin L,
          ∑ k : Fin L, Afield (shiftSite (blockSite L y r) mu k) mu a) • T a := by
    rw [Finset.sum_congr rfl fun r _ => step1 r, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
  rw [step2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, blockAverage_flatTransport]

end Weld

end YangMills
