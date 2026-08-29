import Mathlib
import RequestProject.PascalTower
import RequestProject.ExtensionTowerTree
import RequestProject.SporadicAtlas

/-!
# Modelling the sporadic groups on the tower

The three objects of the construction meet here.

Over a field `GF(q)` of the extension tower, the matrix group of size `n` has order

`|GLₙ(GF(q))| = ∏_{i<n} (qⁿ - qⁱ) = (q-1)ⁿ · q^{C(n,2)} · [n]_q!`

(`SporadicTower.card_GL_eq_glOrd`, `SporadicTower.glOrd_eq_qFact`) — the exponent of `q` is the
Pascal entry `C(n, 2)` and the last factor is the `q`-factorial from the Gaussian triangle, so the
group orders of the tower are read straight off the triangle of
`RequestProject/PascalTower.lean`.

That gives every finite group a *floor* on the tower.  If a group of order `m` acts faithfully by
`n × n` matrices over `GF(q)`, then Lagrange forces `m ∣ |GLₙ(GF(q))|`
(`SporadicTower.dvd_glOrd_of_injective`), and since `|GLₙ|` divides `|GL_{n+1}|`
(`SporadicTower.glOrd_dvd_of_le`) the set of admissible `n` is an up-set with a least element:
the floor `SporadicTower.IsTowerFloor`.

For each of the 26 sporadic groups the floor over `GF(2)` and over `GF(4)` is computed and
kernel-checked here (`SporadicTower.isTowerFloor_gf2`, `SporadicTower.isTowerFloor_gf4`), and the
consequence is recorded in `SporadicTower.dim_ge_floor_gf2` and `SporadicTower.dim_ge_floor_gf4`:
*no* group of that order — hence no copy of that sporadic group — acts faithfully by matrices of
smaller size over those two fields.  For instance the Monster needs at least `58` dimensions over
`GF(2)` and at least `35` over `GF(4)`, and the Lyons group at least `66` over `GF(2)`.

These are lower bounds proved from the order alone; they are not claims about the true minimal
faithful representations, which are larger.
-/

namespace SporadicTower

open Matrix

/-! ## The order of `GLₙ` over a finite field -/

/-- `|GLₙ(GF(q))|`, built up one dimension at a time:
`|GL₀| = 1` and `|GL_{n+1}| = (q^{n+1} - 1) · qⁿ · |GLₙ|`. -/
def glOrd (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => (q ^ (n + 1) - 1) * q ^ n * glOrd q n

@[simp] theorem glOrd_zero (q : Nat) : glOrd q 0 = 1 := rfl

theorem glOrd_succ (q n : Nat) : glOrd q (n + 1) = (q ^ (n + 1) - 1) * q ^ n * glOrd q n := rfl

/-- The closed product formula `|GLₙ| = ∏_{i<n} (qⁿ - qⁱ)`. -/
theorem glOrd_eq_prod (q n : Nat) : ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) = glOrd q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hterm : ∀ i : Fin n,
        q ^ (n + 1) - q ^ ((i.succ : Fin (n + 1)) : ℕ) = q * (q ^ n - q ^ (i : ℕ)) := by
      intro i
      have hi : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
      rw [hi, Nat.mul_sub, ← pow_succ', ← pow_succ']
    simp only [hterm]
    rw [Finset.prod_mul_distrib, ih]
    simp [glOrd_succ]
    ring

/-- `|GLₙ(K)| = glOrd |K| n` for every finite field `K` — in particular for every field of the
extension tower. -/
theorem card_GL_eq_glOrd (K : Type*) [Field K] [Finite K] (n : Nat) :
    Nat.card (GL (Fin n) K) = glOrd (Nat.card K) n := by
  have : Fintype K := Fintype.ofFinite K
  rw [card_GL_field, Nat.card_eq_fintype_card]
  exact glOrd_eq_prod _ n

/-- The order of `GLₙ` in terms of the Gaussian triangle: `(q-1)ⁿ · q^{C(n,2)} · [n]_q!`.  The
exponent of `q` is an entry of Pascal's triangle and `[n]_q!` is built from the `q`-integers, i.e.
from the second column of the Gaussian triangle. -/
theorem glOrd_eq_qFact (q n : Nat) (hq : 1 ≤ q) :
    glOrd q n = (q - 1) ^ n * q ^ (n.choose 2) * PascalTower.qFact q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgeom : PascalTower.qInt q (n + 1) * (q - 1) = q ^ (n + 1) - 1 := by
      have h := PascalTower.geom_sum_mul_pred q (n + 1) hq
      have : PascalTower.qInt q (n + 1) * (q - 1) + 1 = q ^ (n + 1) := h
      omega
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ n 1]
      simp [Nat.choose_one_right]
      omega
    rw [glOrd_succ, ih, PascalTower.qFact_succ, hchoose, ← hgeom]
    ring

/-! ## Floors: `|GLₙ|` divides `|GL_{n+1}|` -/

theorem glOrd_dvd_succ (q n : Nat) : glOrd q n ∣ glOrd q (n + 1) :=
  ⟨(q ^ (n + 1) - 1) * q ^ n, by rw [glOrd_succ]; ring⟩

theorem glOrd_dvd_of_le {q m n : Nat} (h : m ≤ n) : glOrd q m ∣ glOrd q n := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact dvd_trans (ih (by omega)) (glOrd_dvd_succ q n)
    · have : m = n + 1 := by omega
      subst this
      exact dvd_rfl

/-- `N` is the floor of a group of order `m` on the `GF(q)`-tower: the least matrix size over
`GF(q)` whose general linear group is big enough (in the sense of Lagrange) to contain it. -/
def IsTowerFloor (q m N : Nat) : Prop :=
  m ∣ glOrd q N ∧ ∀ n < N, ¬ m ∣ glOrd q n

/-- Because `|GLₙ|` divides `|GL_{n+1}|`, one failure at `N - 1` is enough to pin the floor. -/
theorem isTowerFloor_of {q m N : Nat} (hN : 0 < N) (hdvd : m ∣ glOrd q N)
    (hfail : ¬ m ∣ glOrd q (N - 1)) : IsTowerFloor q m N := by
  refine ⟨hdvd, fun n hn hdvd' => hfail ?_⟩
  exact dvd_trans hdvd' (glOrd_dvd_of_le (by omega))

/-! ## Lagrange: a faithful matrix representation forces divisibility -/

/-- If a finite group embeds in `GLₙ(K)` then its order divides `|GLₙ(K)| = glOrd |K| n`. -/
theorem dvd_glOrd_of_injective {G : Type*} [Group G] [Finite G] {K : Type*} [Field K] [Finite K]
    {n : Nat} (f : G →* GL (Fin n) K) (hf : Function.Injective f) :
    Nat.card G ∣ glOrd (Nat.card K) n := by
  have h := Subgroup.card_dvd_of_injective f hf
  rwa [card_GL_eq_glOrd] at h

/-- **The floor bound.**  A finite group whose order has floor `N` on the `GF(q)`-tower has no
faithful representation by matrices of size smaller than `N` over any field of that size. -/
theorem le_of_injective_of_isTowerFloor {G : Type*} [Group G] [Finite G] {K : Type*} [Field K]
    [Finite K] {n N : Nat} (hfloor : IsTowerFloor (Nat.card K) (Nat.card G) N)
    (f : G →* GL (Fin n) K) (hf : Function.Injective f) : N ≤ n := by
  by_contra hlt
  exact hfloor.2 n (by omega) (dvd_glOrd_of_injective f hf)

/-! ## The 26 floors over `GF(2)` and over `GF(4)` -/

open Sporadic

/-- The floor of each sporadic group on the `GF(2)` tower. -/
def floorGF2 : Group → Nat
  | .M11 => 10 | .M12 => 10 | .J1 => 18 | .M22 => 10 | .J2 => 8 | .M23 => 11
  | .HS => 12 | .J3 => 18 | .M24 => 11 | .McL => 12 | .He => 9 | .Ru => 28
  | .Suz => 12 | .ON => 18 | .Co3 => 12 | .Co2 => 12 | .Fi22 => 14 | .HN => 20
  | .Ly => 66 | .Th => 18 | .Fi23 => 18 | .Co1 => 16 | .J4 => 36
  | .Fi24prime => 28 | .B => 23 | .M => 58

/-- The floor of each sporadic group on the `GF(4)` tower. -/
def floorGF4 : Group → Nat
  | .M11 => 5 | .M12 => 5 | .J1 => 9 | .M22 => 5 | .J2 => 4 | .M23 => 11
  | .HS => 6 | .J3 => 9 | .M24 => 11 | .McL => 6 | .He => 9 | .Ru => 14
  | .Suz => 6 | .ON => 9 | .Co3 => 11 | .Co2 => 11 | .Fi22 => 7 | .HN => 10
  | .Ly => 33 | .Th => 9 | .Fi23 => 11 | .Co1 => 11 | .J4 => 18
  | .Fi24prime => 14 | .B => 23 | .M => 35

set_option maxRecDepth 100000 in
/-- Each of the 26 floors over `GF(2)`, checked by the kernel. -/
theorem isTowerFloor_gf2 (S : Group) : IsTowerFloor 2 S.order (floorGF2 S) := by
  cases S <;>
    exact isTowerFloor_of (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- Each of the 26 floors over `GF(4)`, checked by the kernel. -/
theorem isTowerFloor_gf4 (S : Group) : IsTowerFloor 4 S.order (floorGF4 S) := by
  cases S <;>
    exact isTowerFloor_of (by decide) (by decide) (by decide)

/-- **The sporadic groups on the `GF(2)` floor of the tower.**  No group of sporadic order `S`
acts faithfully by `n × n` matrices over a field of two elements with `n < floorGF2 S`. -/
theorem dim_ge_floor_gf2 {G : Type*} [Group G] [Finite G] {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) (S : Group) (hG : Nat.card G = S.order) {n : Nat}
    (f : G →* GL (Fin n) K) (hf : Function.Injective f) : floorGF2 S ≤ n := by
  refine le_of_injective_of_isTowerFloor ?_ f hf
  rw [hK, hG]
  exact isTowerFloor_gf2 S

/-- **The sporadic groups on the `GF(4)` floor of the tower.** -/
theorem dim_ge_floor_gf4 {G : Type*} [Group G] [Finite G] {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 4) (S : Group) (hG : Nat.card G = S.order) {n : Nat}
    (f : G →* GL (Fin n) K) (hf : Function.Injective f) : floorGF4 S ≤ n := by
  refine le_of_injective_of_isTowerFloor ?_ f hf
  rw [hK, hG]
  exact isTowerFloor_gf4 S

/-- Passing from `GF(2)` up one floor of the tower to `GF(4)` never costs dimensions, and for
most of the sporadic groups it saves some. -/
theorem floorGF4_le_floorGF2 (S : Group) : floorGF4 S ≤ floorGF2 S := by
  cases S <;> decide

/-- The Monster: at least 58 dimensions over `GF(2)`. -/
theorem monster_gf2 {G : Type*} [Group G] [Finite G] {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) (hG : Nat.card G = Group.M.order) {n : Nat}
    (f : G →* GL (Fin n) K) (hf : Function.Injective f) : 58 ≤ n :=
  dim_ge_floor_gf2 hK Group.M hG f hf

/-- The geometry a sporadic group needs at its `GF(2)` floor, read off the Gaussian triangle: the
number of lines of `GF(2)^{floorGF2 S}` is the triangle entry `[floorGF2 S choose 1]₂`. -/
theorem lines_at_floor_gf2 (S : Group) :
    PascalTower.gauss 2 (floorGF2 S) 1 = 2 ^ (floorGF2 S) - 1 := by
  have h := PascalTower.gauss_one_mul_pred 2 (floorGF2 S) (by norm_num)
  omega

/-- The Lyons group has the largest `GF(2)` floor of the atlas, `66`, even though its order is far
from the largest: the primes `37` and `67` dividing `|Ly|` force a large dimension. -/
theorem lyons_gf2_largest_floor (S : Group) : floorGF2 S ≤ floorGF2 Group.Ly := by
  cases S <;> decide

end SporadicTower
