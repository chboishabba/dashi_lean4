/-
# The Wilson plaquette under the time reflection

The reflection `confRefl` of `OS/LinkReflection.lean`, instantiated with the
lattice data of `OS/LatticeGeometry.lean`, acts on the literal Wilson plaquette
holonomies of `Lattice/Wilson.lean` as follows:

* a purely spatial plaquette at `x` is carried to the plaquette at the reflected
  site `siteRefl x`;
* a temporal plaquette at `x` is carried to the *inverse* of the plaquette at
  `siteRefl x - ê₀`, conjugated by a link variable.

Consequently, for a conjugation-invariant character with `χ(g⁻¹) = χ(g)` — the
physical case `χ = Re tr` — the character of every reflected plaquette is the
character of a plaquette of the original configuration, based at

```
  reflBase x mu nu = siteRefl x - ê₀   (temporal plaquettes)
  reflBase x mu nu = siteRefl x        (spatial plaquettes).
```

This is `chi_plaqHol_confRefl`, the geometric input of reflection positivity.
Also proved here: `plaqHol_swap` (exchanging the two directions inverts the
holonomy) and `plaqHol_diag` (a degenerate plaquette is trivial), and
`tval_add_spatial`, `tval_add_time` for the time coordinate of shifted sites.
-/
import Mathlib
import RequestProject.YangMills.OS.LatticeGeometry

namespace RequestProject.YangMills.OS

open RequestProject.YangMills.Lattice

variable {n L : ℕ}

/-! ## Time coordinates of shifted sites -/

theorem tval_add_spatial (x : Site n) {d : Fin 4} (hd : d ≠ 0) :
    tval (x + unitVec n d) = tval x := by
  have h : (unitVec n d) 0 = 0 := by simp [unitVec_apply, Ne.symm hd]
  simp [tval, h]

theorem tval_add_time (x : Site n) (h : tval x + 1 < n + 1) :
    tval (x + unitVec n 0) = tval x + 1 := by
  have h1 : (unitVec n 0) 0 = 1 := by simp [unitVec_apply]
  have hx : x 0 = ((tval x : ℕ) : ZMod (n + 1)) := by
    simp [tval, ZMod.natCast_val, ZMod.cast_id]
  have : (x + unitVec n 0) 0 = ((tval x + 1 : ℕ) : ZMod (n + 1)) := by
    simp only [Pi.add_apply, h1, hx]
    push_cast
    ring
  simp only [tval, this]
  exact ZMod.val_natCast_of_lt h

/-! ## Elementary identities for the plaquette -/

variable {G : Type*} [Group G]

theorem plaqHol_swap (U : Conf n G) (x : Site n) (mu nu : Fin 4) :
    plaqHol U x nu mu = (plaqHol U x mu nu)⁻¹ := by
  simp only [plaqHol, mul_inv_rev, inv_inv]
  group

theorem plaqHol_diag (U : Conf n G) (x : Site n) (mu : Fin 4) :
    plaqHol U x mu mu = 1 := by
  simp only [plaqHol]
  group

/-! ## The reflected configuration -/

/-- The reflected configuration: the literal time reflection of the Wilson
lattice gauge field. -/
noncomputable def reflConf (hN : n + 1 = 2 * L) (U : Conf n G) : Conf n G :=
  (wilsonReflData hN).confRefl U

theorem reflConf_space (hN : n + 1 = 2 * L) (U : Conf n G) (x : Site n) {d : Fin 4}
    (hd : d ≠ 0) : reflConf hN U (x, d) = U (siteRefl x, d) := by
  have hmem : ((x, d) : Link n) ∉ temporalLinks n := by simp [hd]
  simp [reflConf, LinkReflectionData.confRefl, hmem, linkRefl, hd]

theorem reflConf_time (hN : n + 1 = 2 * L) (U : Conf n G) (x : Site n) :
    reflConf hN U (x, 0) = (U (siteRefl x - unitVec n 0, 0))⁻¹ := by
  have hmem : ((x, 0) : Link n) ∈ temporalLinks n := by simp
  simp [reflConf, LinkReflectionData.confRefl, hmem, linkRefl]

/-- The base point of the plaquette that the reflection produces. -/
def reflBase (x : Site n) (mu nu : Fin 4) : Site n :=
  if mu = 0 ∨ nu = 0 then siteRefl x - unitVec n 0 else siteRefl x

/-- A purely spatial reflected plaquette is the plaquette at the reflected
site. -/
theorem plaqHol_reflConf_space (hN : n + 1 = 2 * L) (U : Conf n G) (x : Site n)
    {mu nu : Fin 4} (hmu : mu ≠ 0) (hnu : nu ≠ 0) :
    plaqHol (reflConf hN U) x mu nu = plaqHol U (siteRefl x) mu nu := by
  simp only [plaqHol]
  rw [reflConf_space hN U x hmu, reflConf_space hN U _ hnu, reflConf_space hN U _ hmu,
    reflConf_space hN U x hnu, siteRefl_add_spatial x hmu, siteRefl_add_spatial x hnu]

/-- A temporal reflected plaquette is the inverse of a plaquette of the original
configuration, conjugated by a link variable. -/
theorem plaqHol_reflConf_time (hN : n + 1 = 2 * L) (U : Conf n G) (x : Site n)
    {i : Fin 4} (hi : i ≠ 0) :
    plaqHol (reflConf hN U) x 0 i
      = (U (siteRefl x - unitVec n 0, 0))⁻¹ *
          (plaqHol U (siteRefl x - unitVec n 0) 0 i)⁻¹ *
          U (siteRefl x - unitVec n 0, 0) := by
  set y : Site n := siteRefl x - unitVec n 0 with hy
  have hxy : siteRefl x = y + unitVec n 0 := by rw [hy]; abel
  have h1 : reflConf hN U (x, 0) = (U (y, 0))⁻¹ := reflConf_time hN U x
  have h2 : reflConf hN U (x + unitVec n 0, i) = U (y, i) := by
    rw [reflConf_space hN U _ hi, siteRefl_add_time x]
  have h3 : reflConf hN U (x + unitVec n i, 0) = (U (y + unitVec n i, 0))⁻¹ := by
    rw [reflConf_time hN U _, siteRefl_add_spatial x hi]
    congr 2
    rw [hy]; abel
  have h4 : reflConf hN U (x, i) = U (y + unitVec n 0, i) := by
    rw [reflConf_space hN U x hi, hxy]
  simp only [plaqHol, h1, h2, h3, h4, inv_inv, mul_inv_rev]
  group

/-- **The character of a reflected plaquette is the character of a plaquette.**
This is the geometric identity behind reflection positivity of the Wilson
measure. -/
theorem chi_plaqHol_confRefl (hN : n + 1 = 2 * L) {chi : G → ℝ}
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (hinv : ∀ g : G, chi g⁻¹ = chi g)
    (U : Conf n G) (x : Site n) (mu nu : Fin 4) :
    chi (plaqHol (reflConf hN U) x mu nu) = chi (plaqHol U (reflBase x mu nu) mu nu) := by
  have hconj' : ∀ a g : G, chi (a⁻¹ * g * a) = chi g := by
    intro a g
    simpa using hconj a⁻¹ g
  have hcase1 : ∀ i : Fin 4, i ≠ 0 →
      chi (plaqHol (reflConf hN U) x 0 i)
        = chi (plaqHol U (siteRefl x - unitVec n 0) 0 i) := by
    intro i hi
    rw [plaqHol_reflConf_time hN U x hi, hconj', hinv]
  by_cases hmunu : mu = nu
  · subst hmunu
    rw [plaqHol_diag, plaqHol_diag]
  by_cases hmu : mu = 0
  · subst hmu
    have hnu : nu ≠ 0 := fun hc => hmunu hc.symm
    have hbase : reflBase x 0 nu = siteRefl x - unitVec n 0 := by simp [reflBase]
    rw [hbase]
    exact hcase1 nu hnu
  · by_cases hnu : nu = 0
    · subst hnu
      have hbase : reflBase x mu 0 = siteRefl x - unitVec n 0 := by simp [reflBase]
      rw [hbase]
      calc chi (plaqHol (reflConf hN U) x mu 0)
          = chi ((plaqHol (reflConf hN U) x 0 mu)⁻¹) := by rw [plaqHol_swap]
        _ = chi (plaqHol (reflConf hN U) x 0 mu) := hinv _
        _ = chi (plaqHol U (siteRefl x - unitVec n 0) 0 mu) := hcase1 mu hmu
        _ = chi ((plaqHol U (siteRefl x - unitVec n 0) mu 0)⁻¹) := by rw [plaqHol_swap]
        _ = chi (plaqHol U (siteRefl x - unitVec n 0) mu 0) := hinv _
    · have hbase : reflBase x mu nu = siteRefl x := by simp [reflBase, hmu, hnu]
      rw [hbase, plaqHol_reflConf_space hN U x hmu hnu]

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms plaqHol_reflConf_space
#print axioms plaqHol_reflConf_time
#print axioms chi_plaqHol_confRefl

end Audit
