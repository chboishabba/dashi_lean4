/-
# The whole picture in three dimensions

Everything drawn so far — the ζ-polygon `∑_{n ≤ N} n^{-s}`, the fifteen factor spirals of the
Monster, the twenty-four threads, the twenty-six sporadic orders — has been drawn *flat*, in the
complex plane, where the different objects overlap and only their turning tells them apart.
This file adds the missing coordinate: **height**.

Give the term `n^{-s}` the height `log n`.  Then, at `s = σ + it`,

```
n^{-s} = e^{-σ log n} · e^{-i t log n},
```

so the lifted point `(Re n^{-s}, Im n^{-s}, log n)` lies on the single curve

```
H(z) = e^{-(σ + it) z},   z = height,
```

a **conical helix** on the exponential horn `r = e^{-σz}`, turning at the constant rate `t`
radians per unit of height (`helixC_add`, `norm_helixC`, `natCast_cpow_eq_helixC`).  In three
dimensions the flat picture is one universal curve, and *every* object of this project is a set
of heights on it:

* a prime `p` contributes the arithmetic progression of heights `j·log p`
  (`factorTerm_eq_helixC`) — the factor spiral of `p` is the helix sampled at that progression,
  and this is why it is equiangular;
* the Monster's divisor sum is the sum of the helix over the heights `log d`, `d ∣ |M|`
  (`monsterSpiral_eq_sum_helix`), of which the fiber of `2` occupies the forty-seven heights
  `0, log 2, …, 46 log 2` topping out at `31.88 < 46 log 2 < 31.89` (`two_fiber_top_height`);
* the whole of `|M|` sits at height `124 < log|M| < 125` (`monster_height_bounds`), which is
  exactly the sum of the fifteen prime heights `v_p(|M|)·log p` (`monster_height_eq_sum`) — in
  three dimensions the fifteen factor spirals *stack*;
* the twenty-six sporadic groups occupy twenty-six distinct heights between `log|M_11| = 8.98`
  and `log|M|` (`sporadic_height_bounds`, `sporadic_heights_nodup`);
* the total turning of the ζ-spiral truncated at `N` is `t` times the height of its last vertex
  (`zeta_turning_eq_t_mul_height`), which for `N = |M|` is the Monster's turning budget
  `t·log|M|` of `MonsterSpiral.monster_total_turning`.

Finally the curve is a **loxodrome** on its horn: the angle turned is a constant multiple `t/σ`
of the logarithm of the radius (`helix_loxodrome`), so unrolling the horn makes the whole
picture a straight line (`log_norm_helixC`).

The pictures are `visualization/monster-spiral-3d.svg` (six projected panels),
`visualization/monster-spiral-3d.html` (the same scene, rotatable) and
`visualization/monster-spiral-3d.obj` (the curves as 3D polylines), all rendered by
`RequestProject/MonsterSpiral3DSvg.lean`.
-/
import Mathlib
import RequestProject.MonsterSpiral

open Complex Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MonsterSpiral3D

open Sporadic MonsterSpiral

/-! ## The universal helix -/

/-- **The universal helix** `H(z) = e^{-(σ+it)z}`, parametrised by the *height* `z`.
Every Dirichlet term `n^{-s}` of this project is the value `H(log n)`. -/
noncomputable def helixC (sigma t z : ℝ) : ℂ := Complex.exp (-((sigma : ℂ) + t * Complex.I) * z)

/-- The lift of a complex number to the height `z` in `ℝ³`. -/
def lift3 (w : ℂ) (z : ℝ) : ℝ × ℝ × ℝ := (w.re, w.im, z)

/-- The universal helix as a curve in `ℝ³`: the plane curve at its own height. -/
noncomputable def helix3 (sigma t z : ℝ) : ℝ × ℝ × ℝ := lift3 (helixC sigma t z) z

@[simp] theorem helix3_fst (sigma t z : ℝ) : (helix3 sigma t z).1 = (helixC sigma t z).re := rfl

@[simp] theorem helix3_snd_fst (sigma t z : ℝ) :
    (helix3 sigma t z).2.1 = (helixC sigma t z).im := rfl

/-- The third coordinate of the lifted curve *is* the height. -/
@[simp] theorem helix3_height (sigma t z : ℝ) : (helix3 sigma t z).2.2 = z := rfl

/-- The helix starts at `1` (height `0`, the term `n = 1`). -/
@[simp] theorem helixC_zero (sigma t : ℝ) : helixC sigma t 0 = 1 := by
  simp [helixC]

/-- **The helix is a one-parameter group in the height.**  Translating the height by `w`
multiplies the point by `H(w)`: the curve is self-similar under the screw motion that raises
the height by `w`, scales by `e^{-σw}` and rotates by `-tw`. -/
theorem helixC_add (sigma t z w : ℝ) :
    helixC sigma t (z + w) = helixC sigma t z * helixC sigma t w := by
  rw [helixC, helixC, helixC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The polar form: modulus `e^{-σz}`, argument `-tz`. -/
theorem helixC_polar (sigma t z : ℝ) :
    helixC sigma t z = (Real.exp (-(sigma * z)) : ℝ) * Complex.exp (-(t * z) * Complex.I) := by
  rw [helixC, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The helix lies on the exponential horn `r = e^{-σz}`.** -/
theorem norm_helixC (sigma t z : ℝ) : ‖helixC sigma t z‖ = Real.exp (-(sigma * z)) := by
  rw [helixC, Complex.norm_exp]
  congr 1
  simp

/-- The same statement in `ℝ³`: the distance of `helix3 σ t z` from the vertical axis is
`e^{-σz}`, a function of its height alone. -/
theorem helix3_radius (sigma t z : ℝ) :
    Real.sqrt ((helix3 sigma t z).1 ^ 2 + (helix3 sigma t z).2.1 ^ 2)
      = Real.exp (-(sigma * z)) := by
  rw [helix3_fst, helix3_snd_fst, ← Complex.norm_eq_sqrt_sq_add_sq, norm_helixC]

/-- **Unrolling the horn.**  The logarithm of the radius is a linear function of the height:
in the coordinates `(log r, angle, z)` the whole picture is a straight line. -/
theorem log_norm_helixC (sigma t z : ℝ) : Real.log ‖helixC sigma t z‖ = -(sigma * z) := by
  rw [norm_helixC, Real.log_exp]

/-- **The screw motion.**  Raising the height by `w` scales by `e^{-σw}` and rotates by the
angle `-tw`, whatever the height one starts from: the turning per unit of height is the
constant `t`. -/
theorem helixC_shift (sigma t z w : ℝ) :
    helixC sigma t (z + w)
      = ((Real.exp (-(sigma * w)) : ℝ) : ℂ) * Complex.exp (-(t * w) * Complex.I) *
          helixC sigma t z := by
  rw [helixC_add, ← helixC_polar]
  ring

/-- **The helix is a loxodrome on its horn**: for `σ ≠ 0` the angle turned is the constant
multiple `t/σ` of the logarithm of the radius, so the curve cuts every meridian of the horn at
the same angle. -/
theorem helix_loxodrome {sigma : ℝ} (hs : sigma ≠ 0) (t z : ℝ) :
    -(t * z) = (t / sigma) * Real.log ‖helixC sigma t z‖ := by
  rw [log_norm_helixC]
  field_simp

/-- The velocity of the helix in the height: `H'(z) = -(σ+it)·H(z)`, of constant direction
relative to the point — the 3D tangent makes a constant angle with the axis. -/
theorem hasDerivAt_helixC (sigma t z : ℝ) :
    HasDerivAt (fun z : ℝ => helixC sigma t z)
      (-((sigma : ℂ) + t * Complex.I) * helixC sigma t z) z := by
  have h1 : HasDerivAt (fun z : ℝ => -((sigma : ℂ) + t * Complex.I) * (z : ℂ))
      (-((sigma : ℂ) + t * Complex.I)) z := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := z)).const_mul
      (-((sigma : ℂ) + t * Complex.I))
  simpa [helixC, mul_comm] using h1.cexp

/-! ## Every Dirichlet term is a point of the helix -/

/-- **The lift.**  For `n ≥ 1` the term `n^{-s}` of a Dirichlet series is the point of the
universal helix at height `log n`. -/
theorem natCast_cpow_eq_helixC {n : ℕ} (hn : 1 ≤ n) (sigma t : ℝ) :
    (n : ℂ) ^ (-((sigma : ℂ) + t * Complex.I)) = helixC sigma t (Real.log n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [MoonshineZoom.cpow_neg_eq_polar hn sigma t, helixC_polar,
    Real.rpow_def_of_pos hnpos]
  norm_num
  ring_nf

/-- The 3D lift of the `n`-th term of the ζ-polygon is the point of the helix at height
`log n`. -/
theorem lift3_natCast_cpow {n : ℕ} (hn : 1 ≤ n) (sigma t : ℝ) :
    lift3 ((n : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))) (Real.log n)
      = helix3 sigma t (Real.log n) := by
  rw [helix3, natCast_cpow_eq_helixC hn]

/-- **A prime is an arithmetic progression of heights.**  The `j`-th step of the factor spiral
of `p` is the helix at height `j·log p`; this is why the factor spirals are equiangular, while
the ζ-polygon, whose heights `log n` are irregular, is not. -/
theorem factorTerm_eq_helixC {p : ℕ} (hp : 1 ≤ p) (j : ℕ) (sigma t : ℝ) :
    factorTerm p j ((sigma : ℂ) + t * Complex.I) = helixC sigma t (j * Real.log p) := by
  have hpj : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp
  rw [factorTerm, natCast_cpow_eq_helixC hpj]
  congr 1
  push_cast
  rw [Real.log_pow]

/-- The factor spiral of `p` is the helix sampled at the heights `0, log p, …, e·log p`. -/
theorem factorSpiral_eq_sum_helix {p : ℕ} (hp : 1 ≤ p) (e : ℕ) (sigma t : ℝ) :
    factorSpiral p e ((sigma : ℂ) + t * Complex.I)
      = ∑ j ∈ Finset.range (e + 1), helixC sigma t (j * Real.log p) :=
  Finset.sum_congr rfl fun j _ => factorTerm_eq_helixC hp j sigma t

/-! ## The Monster in three dimensions -/

/-- **The Monster is a set of heights.**  Its divisor-sum polygon is the sum of the universal
helix over the `424 488 960` heights `log d`, `d ∣ |M|`. -/
theorem monsterSpiral_eq_sum_helix (sigma t : ℝ) :
    monsterSpiral ((sigma : ℂ) + t * Complex.I)
      = ∑ d ∈ monsterOrder.divisors, helixC sigma t (Real.log d) := by
  rw [monsterSpiral, divisorSumC]
  refine Finset.sum_congr rfl fun d hd => ?_
  exact natCast_cpow_eq_helixC (Nat.pos_of_mem_divisors hd) sigma t

/-- **The heights of the fiber of `2`**: the forty-six exponents of `2` in `|M|` are the
forty-six heights `k·log 2`, `1 ≤ k ≤ 46`, evenly spaced up the horn. -/
theorem two_fiber_heights (k : ℕ) (sigma t : ℝ) :
    factorTerm 2 k ((sigma : ℂ) + t * Complex.I) = helixC sigma t (k * Real.log 2) :=
  factorTerm_eq_helixC (by norm_num) k sigma t

/-- The top of the fiber of `2`: `2^46` sits at height `46·log 2 ∈ (31.88, 31.89)`. -/
theorem two_fiber_top_height : (31.88 : ℝ) < 46 * Real.log 2 ∧ 46 * Real.log 2 < 31.89 := by
  have h : Real.log (70368744177664 : ℝ) = 46 * Real.log 2 := by
    rw [← twoPow46_eq, Real.log_pow]
    norm_num
  exact ⟨h ▸ log_twoPow46_gt, h ▸ log_twoPow46_lt⟩

/-- **The total height of the Monster**, `124 < log|M| < 125`. -/
theorem monster_height_bounds :
    (124 : ℝ) < Real.log (monsterOrder : ℝ) ∧ Real.log (monsterOrder : ℝ) < 125 :=
  ⟨log_monsterOrder_gt, log_monsterOrder_lt⟩

/-- **The fifteen factor spirals stack.**  The Monster's height is the sum of the fifteen prime
heights `v_p(|M|)·log p`: in three dimensions the separation of `MonsterSpiral` is a
decomposition of one interval of heights into fifteen pieces. -/
theorem monster_height_eq_sum :
    Real.log (monsterOrder : ℝ)
      = ∑ p ∈ monsterPrimes, (monsterOrder.factorization p : ℝ) * Real.log p :=
  log_monsterOrder_eq_sum

/-- **Turning is height.**  The total turning of the ζ-polygon truncated at `N` is `t` times the
height of its last vertex — the universal statement behind `MoonshineZoom.sum_turn` and
`MonsterSpiral.monster_total_turning`. -/
theorem zeta_turning_eq_t_mul_height (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ico 1 N, MoonshineZoom.turn t n = t * Real.log N :=
  MoonshineZoom.sum_turn t N hN

/-- At `N = |M|` that height is the Monster's, so the Monster's turning budget is `t·log|M|`. -/
theorem monster_turning_eq_t_mul_height (t : ℝ) :
    ∑ p ∈ monsterPrimes, (monsterOrder.factorization p : ℝ) * factorTurn t p
      = t * Real.log (monsterOrder : ℝ) :=
  monster_total_turning t

/-! ## The twenty-six sporadic groups as twenty-six heights -/

/-- The height at which a group sits on the horn: `log |G|`. -/
noncomputable def groupHeight (G : Group) : ℝ := Real.log (G.order : ℝ)

/-- The lifted point of the group `G`: the term `|G|^{-s}` at its own height. -/
theorem lift3_groupHeight {G : Group} (hG : G ∈ groups) (sigma t : ℝ) :
    lift3 ((G.order : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))) (groupHeight G)
      = helix3 sigma t (groupHeight G) :=
  lift3_natCast_cpow (Nat.one_le_iff_ne_zero.mpr (order_ne_zero hG)) sigma t

/-- **The sporadic tower.**  All twenty-six sporadic groups sit between the heights
`log 7920 = log|M_11|` and `log|M|`. -/
theorem sporadic_height_bounds :
    ∀ G ∈ groups, Real.log 7920 ≤ groupHeight G ∧ groupHeight G ≤ Real.log (monsterOrder : ℝ) := by
  intro G hG
  obtain ⟨h1, h2⟩ := order_mem_Icc G hG
  have h1' : (7920 : ℝ) ≤ (G.order : ℝ) := by exact_mod_cast h1
  have h2' : ((G.order : ℕ) : ℝ) ≤ (monsterOrder : ℝ) := by exact_mod_cast h2
  exact ⟨Real.log_le_log (by norm_num) h1', Real.log_le_log (by linarith) h2'⟩

/-- The heights are strictly increasing in the order of the group. -/
theorem groupHeight_lt_groupHeight {G H : Group} (hG : G ∈ groups)
    (h : G.order < H.order) : groupHeight G < groupHeight H := by
  have hGpos : (0 : ℝ) < (G.order : ℝ) := by
    have := (order_mem_Icc G hG).1
    have : (7920 : ℝ) ≤ (G.order : ℝ) := by exact_mod_cast this
    linarith
  have : ((G.order : ℕ) : ℝ) < (H.order : ℝ) := by exact_mod_cast h
  exact Real.log_lt_log hGpos this

/-- The twenty-six orders are pairwise distinct, so the twenty-six groups occupy twenty-six
distinct heights. -/
theorem sporadic_orders_nodup : (groups.map Group.order).Nodup := by decide

end MonsterSpiral3D
