/-
# The radius expansion of the three-taper `3 × 3` determinant

Each literal channel coordinate is quadratically small in the sampling radius,

    |c - s L| ≤ s² B,        s = r², 0 ≤ s ≤ 1,

(the shape proved in `LiteralWeilTargetDefectLeadingCoefficient`).  For the two-zero
stage the admission certificate is a `3 × 3` determinant of three such vectors, so its
leading term is of order `s³ = r⁶` with a *relative* error of order `s = r²`:

    |det3 x y z - s³ det3 Lx Ly Lz| ≤ s⁴ · det3Remainder.

Consequently the two-nuisance admission test is again a **radius-free coefficient
comparison**:

    s · det3Remainder < |det3 Lx Ly Lz|   ⟹   det3 x y z ≠ 0,

and, by `ThreeTaperSchurCore.elim2_ne_zero_of_det3_ne_zero`, the target survives the
exact elimination of both nuisance directions.

Everything here is elementary algebra with explicit constants; nothing is asserted
about the size of the leading determinant itself.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.ThreeTaperSchurCore

noncomputable section

namespace Zeta23Bridge
namespace ThreeTaperCrossDetLeading

open Zeta23Bridge.ThreeTaperSchurCore

/-! ## One multiplication step -/

/-- **Multiplying a small quantity by a quadratically small channel.**  If
`|A - m L_A| ≤ m s B_A` and `|x - s L_x| ≤ s² B_x`, then the product is controlled at
one order higher. -/
theorem abs_mul_step {A x LA BA Lx Bx s m : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hm0 : 0 ≤ m) (hA : |A - m * LA| ≤ m * s * BA) (hx : |x - s * Lx| ≤ s ^ 2 * Bx)
    (hBA : 0 ≤ BA) (hBx : 0 ≤ Bx) :
    |A * x - m * s * (LA * Lx)| ≤ m * s ^ 2 * (|LA| * Bx + BA * |Lx| + BA * Bx) := by
  have hxabs : |x| ≤ s * |Lx| + s ^ 2 * Bx := by
    have h := abs_sub_abs_le_abs_sub x (s * Lx)
    have hsl : |s * Lx| = s * |Lx| := by rw [abs_mul, abs_of_nonneg hs0]
    linarith [hx, h, hsl.le, hsl.ge]
  have hsplit : A * x - m * s * (LA * Lx)
      = (A - m * LA) * x + (m * LA) * (x - s * Lx) := by ring
  have hb1 : |(A - m * LA) * x| ≤ (m * s * BA) * (s * |Lx| + s ^ 2 * Bx) := by
    rw [abs_mul]
    exact mul_le_mul hA hxabs (abs_nonneg _) (by positivity)
  have hb2 : |(m * LA) * (x - s * Lx)| ≤ (m * |LA|) * (s ^ 2 * Bx) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have htri : |A * x - m * s * (LA * Lx)|
      ≤ (m * s * BA) * (s * |Lx| + s ^ 2 * Bx) + (m * |LA|) * (s ^ 2 * Bx) := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith)
  have habsorb : m * s ^ 3 * (BA * Bx) ≤ m * s ^ 2 * (BA * Bx) := by
    have h1 : (0:ℝ) ≤ s ^ 2 - s ^ 3 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hm0 (mul_nonneg hBA hBx)) h1]
  nlinarith [htri, habsorb]

/-! ## Products of two and three quadratically small channels -/

/-- The explicit remainder constant of a product of two quadratically small channels. -/
def prodRem (Lx Bx Ly By : ℝ) : ℝ := |Lx| * By + Bx * |Ly| + Bx * By

theorem prodRem_nonneg {Lx Bx Ly By : ℝ} (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) :
    0 ≤ prodRem Lx Bx Ly By := by
  unfold prodRem
  have := abs_nonneg Lx
  have := abs_nonneg Ly
  positivity

/-- The explicit remainder constant of a product of three quadratically small channels. -/
def tripleRem (Lx Bx Ly By Lz Bz : ℝ) : ℝ :=
  |Lx * Ly| * Bz + prodRem Lx Bx Ly By * |Lz| + prodRem Lx Bx Ly By * Bz

theorem tripleRem_nonneg {Lx Bx Ly By Lz Bz : ℝ} (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hBz : 0 ≤ Bz) : 0 ≤ tripleRem Lx Bx Ly By Lz Bz := by
  unfold tripleRem
  have h := prodRem_nonneg (Lx := Lx) (Bx := Bx) (Ly := Ly) (By := By) hBx hBy
  have := abs_nonneg (Lx * Ly)
  have := abs_nonneg Lz
  positivity

theorem abs_prod_sub_leading_le {x y Lx Bx Ly By s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : |x - s * Lx| ≤ s ^ 2 * Bx) (hy : |y - s * Ly| ≤ s ^ 2 * By)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) :
    |x * y - s ^ 2 * (Lx * Ly)| ≤ s ^ 3 * prodRem Lx Bx Ly By := by
  have h := abs_mul_step (A := x) (x := y) (LA := Lx) (BA := Bx) (Lx := Ly) (Bx := By)
    (s := s) (m := s) hs0 hs1 hs0 (by simpa [pow_two] using hx) hy hBx hBy
  unfold prodRem
  calc |x * y - s ^ 2 * (Lx * Ly)| = |x * y - s * s * (Lx * Ly)| := by ring_nf
    _ ≤ s * s ^ 2 * (|Lx| * By + Bx * |Ly| + Bx * By) := h
    _ = s ^ 3 * (|Lx| * By + Bx * |Ly| + Bx * By) := by ring

/-- **A product of three quadratically small channels is cubically small in `s`, with an
explicit relative remainder.** -/
theorem abs_triple_sub_leading_le {x y z Lx Bx Ly By Lz Bz s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : |x - s * Lx| ≤ s ^ 2 * Bx) (hy : |y - s * Ly| ≤ s ^ 2 * By)
    (hz : |z - s * Lz| ≤ s ^ 2 * Bz) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hBz : 0 ≤ Bz) :
    |x * y * z - s ^ 3 * (Lx * Ly * Lz)| ≤ s ^ 4 * tripleRem Lx Bx Ly By Lz Bz := by
  have hxy := abs_prod_sub_leading_le hs0 hs1 hx hy hBx hBy
  have hP := prodRem_nonneg (Lx := Lx) (Bx := Bx) (Ly := Ly) (By := By) hBx hBy
  have hm0 : (0 : ℝ) ≤ s ^ 2 := by positivity
  have h := abs_mul_step (A := x * y) (x := z) (LA := Lx * Ly)
    (BA := prodRem Lx Bx Ly By) (Lx := Lz) (Bx := Bz) (s := s) (m := s ^ 2) hs0 hs1 hm0
    (by calc |x * y - s ^ 2 * (Lx * Ly)| ≤ s ^ 3 * prodRem Lx Bx Ly By := hxy
      _ = s ^ 2 * s * prodRem Lx Bx Ly By := by ring) hz hP hBz
  unfold tripleRem
  calc |x * y * z - s ^ 3 * (Lx * Ly * Lz)|
      = |x * y * z - s ^ 2 * s * (Lx * Ly * Lz)| := by ring_nf
    _ ≤ s ^ 2 * s ^ 2 * (|Lx * Ly| * Bz + prodRem Lx Bx Ly By * |Lz|
          + prodRem Lx Bx Ly By * Bz) := h
    _ = s ^ 4 * (|Lx * Ly| * Bz + prodRem Lx Bx Ly By * |Lz|
          + prodRem Lx Bx Ly By * Bz) := by ring

/-! ## The determinant of three quadratically small channel vectors -/

/-- The explicit remainder constant of the three-taper determinant: the sum of the six
triple remainders, one per permutation. -/
def det3Rem (Lx Bx Ly By Lz Bz : Fin 3 → ℝ) : ℝ :=
  tripleRem (Lx 0) (Bx 0) (Ly 1) (By 1) (Lz 2) (Bz 2)
    + tripleRem (Lx 0) (Bx 0) (Ly 2) (By 2) (Lz 1) (Bz 1)
    + tripleRem (Lx 1) (Bx 1) (Ly 0) (By 0) (Lz 2) (Bz 2)
    + tripleRem (Lx 1) (Bx 1) (Ly 2) (By 2) (Lz 0) (Bz 0)
    + tripleRem (Lx 2) (Bx 2) (Ly 0) (By 0) (Lz 1) (Bz 1)
    + tripleRem (Lx 2) (Bx 2) (Ly 1) (By 1) (Lz 0) (Bz 0)

theorem det3Rem_nonneg {Lx Bx Ly By Lz Bz : Fin 3 → ℝ} (hBx : ∀ i, 0 ≤ Bx i)
    (hBy : ∀ i, 0 ≤ By i) (hBz : ∀ i, 0 ≤ Bz i) : 0 ≤ det3Rem Lx Bx Ly By Lz Bz := by
  unfold det3Rem
  have h1 := tripleRem_nonneg (Lx := Lx 0) (Bx := Bx 0) (Ly := Ly 1) (By := By 1)
    (Lz := Lz 2) (Bz := Bz 2) (hBx 0) (hBy 1) (hBz 2)
  have h2 := tripleRem_nonneg (Lx := Lx 0) (Bx := Bx 0) (Ly := Ly 2) (By := By 2)
    (Lz := Lz 1) (Bz := Bz 1) (hBx 0) (hBy 2) (hBz 1)
  have h3 := tripleRem_nonneg (Lx := Lx 1) (Bx := Bx 1) (Ly := Ly 0) (By := By 0)
    (Lz := Lz 2) (Bz := Bz 2) (hBx 1) (hBy 0) (hBz 2)
  have h4 := tripleRem_nonneg (Lx := Lx 1) (Bx := Bx 1) (Ly := Ly 2) (By := By 2)
    (Lz := Lz 0) (Bz := Bz 0) (hBx 1) (hBy 2) (hBz 0)
  have h5 := tripleRem_nonneg (Lx := Lx 2) (Bx := Bx 2) (Ly := Ly 0) (By := By 0)
    (Lz := Lz 1) (Bz := Bz 1) (hBx 2) (hBy 0) (hBz 1)
  have h6 := tripleRem_nonneg (Lx := Lx 2) (Bx := Bx 2) (Ly := Ly 1) (By := By 1)
    (Lz := Lz 0) (Bz := Bz 0) (hBx 2) (hBy 1) (hBz 0)
  linarith

/-- **The three-taper determinant is cubically small in `s = r²`, with the radius-free
leading determinant as its coefficient.** -/
theorem abs_det3_sub_leading_le {x y z Lx Bx Ly By Lz Bz : Fin 3 → ℝ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : ∀ i, |x i - s * Lx i| ≤ s ^ 2 * Bx i)
    (hy : ∀ i, |y i - s * Ly i| ≤ s ^ 2 * By i)
    (hz : ∀ i, |z i - s * Lz i| ≤ s ^ 2 * Bz i)
    (hBx : ∀ i, 0 ≤ Bx i) (hBy : ∀ i, 0 ≤ By i) (hBz : ∀ i, 0 ≤ Bz i) :
    |det3 x y z - s ^ 3 * det3 Lx Ly Lz| ≤ s ^ 4 * det3Rem Lx Bx Ly By Lz Bz := by
  have t1 := abs_le.mp (abs_triple_sub_leading_le hs0 hs1 (hx 0) (hy 1) (hz 2)
    (hBx 0) (hBy 1) (hBz 2))
  have t2 := abs_le.mp (abs_triple_sub_leading_le hs0 hs1 (hx 0) (hy 2) (hz 1)
    (hBx 0) (hBy 2) (hBz 1))
  have t3 := abs_le.mp (abs_triple_sub_leading_le hs0 hs1 (hx 1) (hy 0) (hz 2)
    (hBx 1) (hBy 0) (hBz 2))
  have t4 := abs_le.mp (abs_triple_sub_leading_le hs0 hs1 (hx 1) (hy 2) (hz 0)
    (hBx 1) (hBy 2) (hBz 0))
  have t5 := abs_le.mp (abs_triple_sub_leading_le hs0 hs1 (hx 2) (hy 0) (hz 1)
    (hBx 2) (hBy 0) (hBz 1))
  have t6 := abs_le.mp (abs_triple_sub_leading_le hs0 hs1 (hx 2) (hy 1) (hz 0)
    (hBx 2) (hBy 1) (hBz 0))
  have hdist : s ^ 4 * det3Rem Lx Bx Ly By Lz Bz
      = s ^ 4 * tripleRem (Lx 0) (Bx 0) (Ly 1) (By 1) (Lz 2) (Bz 2)
        + s ^ 4 * tripleRem (Lx 0) (Bx 0) (Ly 2) (By 2) (Lz 1) (Bz 1)
        + s ^ 4 * tripleRem (Lx 1) (Bx 1) (Ly 0) (By 0) (Lz 2) (Bz 2)
        + s ^ 4 * tripleRem (Lx 1) (Bx 1) (Ly 2) (By 2) (Lz 0) (Bz 0)
        + s ^ 4 * tripleRem (Lx 2) (Bx 2) (Ly 0) (By 0) (Lz 1) (Bz 1)
        + s ^ 4 * tripleRem (Lx 2) (Bx 2) (Ly 1) (By 1) (Lz 0) (Bz 0) := by
    unfold det3Rem; ring
  have hkey : det3 x y z - s ^ 3 * det3 Lx Ly Lz
      = (x 0 * y 1 * z 2 - s ^ 3 * (Lx 0 * Ly 1 * Lz 2))
        - (x 0 * y 2 * z 1 - s ^ 3 * (Lx 0 * Ly 2 * Lz 1))
        - (x 1 * y 0 * z 2 - s ^ 3 * (Lx 1 * Ly 0 * Lz 2))
        + (x 1 * y 2 * z 0 - s ^ 3 * (Lx 1 * Ly 2 * Lz 0))
        + (x 2 * y 0 * z 1 - s ^ 3 * (Lx 2 * Ly 0 * Lz 1))
        - (x 2 * y 1 * z 0 - s ^ 3 * (Lx 2 * Ly 1 * Lz 0)) := by
    unfold det3; ring
  rw [hkey, abs_le, hdist]
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2,
    t6.1, t6.2]

/-- **The radius-free coefficient gate for two nuisance zeros.**  If the leading
determinant beats the explicit relative remainder at the scale used, the actual
determinant is nonzero. -/
theorem det3_ne_zero_of_coefficient_gate {x y z Lx Bx Ly By Lz Bz : Fin 3 → ℝ} {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hx : ∀ i, |x i - s * Lx i| ≤ s ^ 2 * Bx i)
    (hy : ∀ i, |y i - s * Ly i| ≤ s ^ 2 * By i)
    (hz : ∀ i, |z i - s * Lz i| ≤ s ^ 2 * Bz i)
    (hBx : ∀ i, 0 ≤ Bx i) (hBy : ∀ i, 0 ≤ By i) (hBz : ∀ i, 0 ≤ Bz i)
    (hgate : s * det3Rem Lx Bx Ly By Lz Bz < |det3 Lx Ly Lz|) :
    det3 x y z ≠ 0 := by
  intro hzero
  have hbd := abs_det3_sub_leading_le hs0.le hs1 hx hy hz hBx hBy hBz
  rw [hzero, zero_sub, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 3)] at hbd
  have hs3 : (0:ℝ) < s ^ 3 := by positivity
  have hlt : s ^ 3 * (s * det3Rem Lx Bx Ly By Lz Bz) < s ^ 3 * |det3 Lx Ly Lz| :=
    mul_lt_mul_of_pos_left hgate hs3
  nlinarith [hbd, hlt]


/-! ## Entrywise perturbation of the determinant

For the two-zero construction the reference matrix is the point-window response matrix,
and the actual matrix differs from it entrywise by a quantity that vanishes as the
windows collapse.  A nonzero reference determinant therefore forces a nonzero actual
determinant, once the entrywise deviation is small enough. -/

theorem abs_triple_sub_triple_le {x y z x' y' z' M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hx' : |x'| ≤ M) (hy' : |y'| ≤ M) (hz' : |z'| ≤ M)
    (hx : |x - x'| ≤ d) (hy : |y - y'| ≤ d) (hz : |z - z'| ≤ d) :
    |x * y * z - x' * y' * z'| ≤ 3 * d * (M + d) ^ 2 := by
  have hyb : |y| ≤ M + d := by
    have := abs_sub_abs_le_abs_sub y y'
    linarith [hy, hy', this]
  have hzb : |z| ≤ M + d := by
    have := abs_sub_abs_le_abs_sub z z'
    linarith [hz, hz', this]
  have hsplit : x * y * z - x' * y' * z'
      = (x - x') * (y * z) + x' * ((y - y') * z) + x' * (y' * (z - z')) := by ring
  have hb1 : |(x - x') * (y * z)| ≤ d * ((M + d) * (M + d)) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hx (mul_le_mul hyb hzb (abs_nonneg _) (by linarith))
      (by positivity) (by linarith)
  have hb2 : |x' * ((y - y') * z)| ≤ M * (d * (M + d)) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hx' (mul_le_mul hy hzb (abs_nonneg _) (by linarith))
      (by positivity) hM
  have hb3 : |x' * (y' * (z - z'))| ≤ M * (M * d) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hx' (mul_le_mul hy' hz (abs_nonneg _) hM) (by positivity) hM
  have htri : |x * y * z - x' * y' * z'|
      ≤ d * ((M + d) * (M + d)) + M * (d * (M + d)) + M * (M * d) := by
    rw [hsplit]
    calc |(x - x') * (y * z) + x' * ((y - y') * z) + x' * (y' * (z - z'))|
        ≤ |(x - x') * (y * z) + x' * ((y - y') * z)| + |x' * (y' * (z - z'))| :=
          abs_add_le _ _
      _ ≤ |(x - x') * (y * z)| + |x' * ((y - y') * z)| + |x' * (y' * (z - z'))| := by
          have := abs_add_le ((x - x') * (y * z)) (x' * ((y - y') * z))
          linarith
      _ ≤ d * ((M + d) * (M + d)) + M * (d * (M + d)) + M * (M * d) := by linarith
  have e1 : M * (d * (M + d)) ≤ d * ((M + d) * (M + d)) := by
    nlinarith [mul_nonneg (mul_nonneg hd hd) (by linarith : (0:ℝ) ≤ M + d)]
  have e2 : M * (M * d) ≤ d * ((M + d) * (M + d)) := by
    nlinarith [mul_nonneg hd (mul_nonneg hM hd), mul_nonneg hd (mul_nonneg hd hd)]
  linarith [htri, e1, e2]

/-- **Entrywise perturbation bound for `det3`.** -/
theorem abs_det3_sub_det3_le {u v w u' v' w' : Fin 3 → ℝ} {M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hu' : ∀ i, |u' i| ≤ M) (hv' : ∀ i, |v' i| ≤ M) (hw' : ∀ i, |w' i| ≤ M)
    (hu : ∀ i, |u i - u' i| ≤ d) (hv : ∀ i, |v i - v' i| ≤ d) (hw : ∀ i, |w i - w' i| ≤ d) :
    |det3 u v w - det3 u' v' w'| ≤ 18 * d * (M + d) ^ 2 := by
  have t1 := abs_le.mp (abs_triple_sub_triple_le hM hd (hu' 0) (hv' 1) (hw' 2)
    (hu 0) (hv 1) (hw 2))
  have t2 := abs_le.mp (abs_triple_sub_triple_le hM hd (hu' 0) (hv' 2) (hw' 1)
    (hu 0) (hv 2) (hw 1))
  have t3 := abs_le.mp (abs_triple_sub_triple_le hM hd (hu' 1) (hv' 0) (hw' 2)
    (hu 1) (hv 0) (hw 2))
  have t4 := abs_le.mp (abs_triple_sub_triple_le hM hd (hu' 1) (hv' 2) (hw' 0)
    (hu 1) (hv 2) (hw 0))
  have t5 := abs_le.mp (abs_triple_sub_triple_le hM hd (hu' 2) (hv' 0) (hw' 1)
    (hu 2) (hv 0) (hw 1))
  have t6 := abs_le.mp (abs_triple_sub_triple_le hM hd (hu' 2) (hv' 1) (hw' 0)
    (hu 2) (hv 1) (hw 0))
  have hkey : det3 u v w - det3 u' v' w'
      = (u 0 * v 1 * w 2 - u' 0 * v' 1 * w' 2) - (u 0 * v 2 * w 1 - u' 0 * v' 2 * w' 1)
        - (u 1 * v 0 * w 2 - u' 1 * v' 0 * w' 2) + (u 1 * v 2 * w 0 - u' 1 * v' 2 * w' 0)
        + (u 2 * v 0 * w 1 - u' 2 * v' 0 * w' 1) - (u 2 * v 1 * w 0 - u' 2 * v' 1 * w' 0) := by
    unfold det3; ring
  rw [hkey, abs_le]
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2,
    t6.1, t6.2]

/-- **A nonzero reference determinant survives a small entrywise perturbation.** -/
theorem det3_ne_zero_of_close {u v w u' v' w' : Fin 3 → ℝ} {M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hu' : ∀ i, |u' i| ≤ M) (hv' : ∀ i, |v' i| ≤ M) (hw' : ∀ i, |w' i| ≤ M)
    (hu : ∀ i, |u i - u' i| ≤ d) (hv : ∀ i, |v i - v' i| ≤ d) (hw : ∀ i, |w i - w' i| ≤ d)
    (hgap : 18 * d * (M + d) ^ 2 < |det3 u' v' w'|) :
    det3 u v w ≠ 0 := by
  intro hzero
  have hbd := abs_det3_sub_det3_le hM hd hu' hv' hw' hu hv hw
  rw [hzero, zero_sub, abs_neg] at hbd
  linarith

end ThreeTaperCrossDetLeading
end Zeta23Bridge
