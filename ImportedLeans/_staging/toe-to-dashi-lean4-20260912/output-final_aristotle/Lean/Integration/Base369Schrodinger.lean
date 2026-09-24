import Integration.Base369Heisenberg

/-!
# The Schrödinger module of the finite Heisenberg group, and its irreducibility

Continuing `Integration.Base369Heisenberg`.  The Schrödinger module of
`H(n) = 𝔽₃ⁿ × (𝔽₃ⁿ)* × 𝔽₃` is

```
V = (𝔽₃ⁿ → ℂ),        (T g f)(u) = χ(z_g + ⟨y_g, u - x_g⟩) · f(u - x_g),
```

with `χ = ZMod.stdAddChar` the standard additive character of `𝔽₃` (a primitive
cube root of unity).  Working over `ℂ` rather than `ℚ(ζ₃)` costs nothing here:
every statement below is about the `ℂ`-module structure, and `ℚ(ζ₃) ⊆ ℂ`.

## What is proved

* `T_one`, `T_mul` — `T` is a genuine action of the group law proved in
  `Base369Heisenberg`: `T g ∘ T h = T (g * h)`.  (The phase convention
  `⟨y, u - x⟩` is exactly the one that matches that group's cocycle.)
* `charSum` — the coordinate Fourier orthogonality
  `∑_{y ∈ 𝔽₃ⁿ} χ⟨y, v⟩ = 3ⁿ · [v = 0]`.
* `proj_eq` — the composed point projector
  `P_x f = ∑_y χ(-⟨y,x⟩) · T(0,y,0) f` satisfies
  **`P_x f = (3ⁿ · f x) • δ_x`**; in particular `P_x f (x) = 3ⁿ f(x)` and
  `P_x f (u) = 0` for `u ≠ x`.
* `delta_mem_of_mem` — hence any nonzero `T`-invariant subspace containing `f`
  contains the delta line at every point where `f` does not vanish.
* `T_translate_delta` — translations move deltas transitively.
* **`schrodinger_irreducible`** — every `T`-invariant `ℂ`-subspace of `V` is
  `⊥` or `⊤`: the Schrödinger module is irreducible.
* `finrank_V` — its dimension is `3ⁿ`, i.e. `729` for `n = 6`
  (`finrank_V6`).

## What this does *not* say

Irreducibility plus a dimension count is **not** an identification of a
representation: `dimension_is_not_identity` records that there are many
pairwise non-isomorphic modules of the same dimension over the same group, so
nothing here supports reading `729` as an identification with any other object.
Stone–von Neumann uniqueness (irreducible modules with a fixed central character
are isomorphic) is *not* proved here.
-/

namespace Integration.Base369Schrodinger

open Finset Integration.Base369Heisenberg

variable {n : ℕ}

/-! ## §1 The character -/

/-- The standard additive character of `𝔽₃`. -/
noncomputable def chi : AddChar F3 ℂ := ZMod.stdAddChar

@[simp] theorem chi_zero : chi (0 : F3) = 1 := chi.map_zero_eq_one

theorem chi_add (a b : F3) : chi (a + b) = chi a * chi b := chi.map_add_eq_mul a b

theorem chi_ne_one {a : F3} (ha : a ≠ 0) : chi a ≠ 1 := by
  intro h
  exact ha (ZMod.injective_stdAddChar (by simpa [chi] using h))

theorem dot_sub_right (y x x' : X n) : dot y (x - x') = dot y x - dot y x' := by
  rw [sub_eq_add_neg, dot_add_right, dot_neg_right, sub_eq_add_neg]

/-- Pairing with a fixed vector, as an additive homomorphism in the first slot. -/
def dotHom (v : X n) : (X n) →+ F3 where
  toFun y := dot y v
  map_zero' := dot_zero_left v
  map_add' y y' := dot_add_left y y' v

/-- The additive character `y ↦ χ⟨y, v⟩` of `𝔽₃ⁿ`. -/
noncomputable def psi (v : X n) : AddChar (X n) ℂ := chi.compAddMonoidHom (dotHom v)

@[simp] theorem psi_apply (v y : X n) : psi v y = chi (dot y v) := rfl

theorem psi_eq_zero_iff (v : X n) : psi v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv (funext hcon)
    have h1 : psi v (e i) = 1 := by rw [h]; rfl
    rw [psi_apply, dot_e_left] at h1
    exact chi_ne_one hi h1
  · rintro rfl
    ext y
    simp [psi_apply]

theorem card_X (n : ℕ) : Fintype.card (X n) = 3 ^ n := by
  simp [X, ZMod.card]

/-- **Coordinate Fourier orthogonality.** -/
theorem charSum (v : X n) :
    (∑ y : X n, chi (dot y v)) = if v = 0 then (3 : ℂ) ^ n else 0 := by
  classical
  have h := AddChar.sum_eq_ite (psi v)
  simp only [psi_apply] at h
  rw [h, card_X]
  by_cases hv : v = 0
  · rw [if_pos ((psi_eq_zero_iff v).2 hv), if_pos hv]
    push_cast
    ring
  · rw [if_neg (fun hc => hv ((psi_eq_zero_iff v).1 hc)), if_neg hv]

/-! ## §2 The Schrödinger action -/

/-- The Schrödinger action of `H n` on `V = 𝔽₃ⁿ → ℂ`. -/
noncomputable def T (g : H n) (f : X n → ℂ) : X n → ℂ :=
  fun u => chi (g.z + dot g.y (u - g.x)) * f (u - g.x)

@[simp] theorem T_one (f : X n → ℂ) : T 1 f = f := by
  funext u
  simp [T]

/-- `T` is an action of the Heisenberg group law. -/
theorem T_mul (g h : H n) (f : X n → ℂ) : T g (T h f) = T (g * h) f := by
  funext u
  have harg : u - g.x - h.x = u - (g * h).x := by
    simp only [mul_x]
    abel
  have hexp : g.z + dot g.y (u - g.x) + (h.z + dot h.y (u - g.x - h.x))
      = (g * h).z + dot (g * h).y (u - (g * h).x) := by
    simp only [mul_x, mul_y, mul_z, dot_sub_right, dot_add_left, dot_add_right]
    ring
  simp only [T]
  rw [← mul_assoc, ← chi_add, hexp, harg]

theorem T_smul (g : H n) (c : ℂ) (f : X n → ℂ) : T g (c • f) = c • T g f := by
  funext u
  simp [T, smul_eq_mul]
  ring

theorem T_add (g : H n) (f f' : X n → ℂ) : T g (f + f') = T g f + T g f' := by
  funext u
  simp [T]
  ring

/-! ## §3 The point projector -/

/-- The delta function at `x`. -/
def delta (x : X n) : X n → ℂ := fun u => if u = x then 1 else 0

/-- The composed coordinate Fourier projector at `x`. -/
noncomputable def proj (x : X n) (f : X n → ℂ) : X n → ℂ :=
  ∑ y : X n, chi (-(dot y x)) • T ⟨0, y, 0⟩ f

theorem proj_apply (x : X n) (f : X n → ℂ) (u : X n) :
    proj x f u = (∑ y : X n, chi (dot y (u - x))) * f u := by
  simp only [proj, Finset.sum_apply, Pi.smul_apply, T, smul_eq_mul, sub_zero, zero_add,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dot_sub_right, sub_eq_add_neg, chi_add]
  ring

/-- **The projector produces the delta line.** -/
theorem proj_eq (x : X n) (f : X n → ℂ) : proj x f = ((3 : ℂ) ^ n * f x) • delta x := by
  funext u
  rw [proj_apply, charSum]
  by_cases h : u = x
  · subst h
    simp [delta]
  · have : u - x ≠ 0 := sub_ne_zero.2 h
    simp [this, delta, h]

theorem proj_self (x : X n) (f : X n → ℂ) : proj x f x = (3 : ℂ) ^ n * f x := by
  rw [proj_eq]
  simp [delta]

theorem proj_other {x u : X n} (f : X n → ℂ) (h : u ≠ x) : proj x f u = 0 := by
  rw [proj_eq]
  simp [delta, h]

/-! ## §4 Irreducibility -/

/-- A subspace closed under a given action of `H n`. -/
def InvariantFor (act : H n → (X n → ℂ) → (X n → ℂ)) (W : Submodule ℂ (X n → ℂ)) : Prop :=
  ∀ g f, f ∈ W → act g f ∈ W

/-- A subspace closed under the Schrödinger action. -/
def Invariant (W : Submodule ℂ (X n → ℂ)) : Prop := InvariantFor T W

theorem proj_mem {W : Submodule ℂ (X n → ℂ)} (hW : Invariant W) {f : X n → ℂ} (hf : f ∈ W)
    (x : X n) : proj x f ∈ W :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (hW _ _ hf)

/-- A nonzero invariant subspace contains the delta line wherever its member does
not vanish. -/
theorem delta_mem_of_mem {W : Submodule ℂ (X n → ℂ)} (hW : Invariant W) {f : X n → ℂ}
    (hf : f ∈ W) {x : X n} (hfx : f x ≠ 0) : delta x ∈ W := by
  have hmem := proj_mem hW hf x
  rw [proj_eq] at hmem
  have hne : ((3 : ℂ) ^ n * f x) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hfx
  have := Submodule.smul_mem W (((3 : ℂ) ^ n * f x)⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this

/-- Translations move deltas transitively. -/
theorem T_translate_delta (a x : X n) : T (⟨a, 0, 0⟩ : H n) (delta x) = delta (x + a) := by
  funext u
  simp only [T, delta, dot_zero_left, add_zero, chi_zero, one_mul]
  by_cases h : u = x + a
  · subst h; simp
  · have : u - a ≠ x := fun hc => h (by rw [← hc]; abel)
    simp [this, h]

/-- Deltas span the module. -/
theorem eq_sum_deltas (f : X n → ℂ) : f = ∑ x : X n, f x • delta x := by
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply, delta, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single u] <;> simp +contextual [eq_comm]

/-- **The Schrödinger module is irreducible.** -/
theorem schrodinger_irreducible {W : Submodule ℂ (X n → ℂ)} (hW : Invariant W) (hne : W ≠ ⊥) :
    W = ⊤ := by
  obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).1 hne
  obtain ⟨x, hfx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf0 (funext hcon)
  have hdx : delta x ∈ W := delta_mem_of_mem hW hfW hfx
  have hall : ∀ z : X n, delta z ∈ W := by
    intro z
    have := hW ⟨z - x, 0, 0⟩ _ hdx
    rwa [T_translate_delta, add_sub_cancel] at this
  refine Submodule.eq_top_iff'.2 fun f' => ?_
  rw [eq_sum_deltas f']
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hall z)

/-! ## §5 Dimension, and what it does not buy -/

theorem finrank_V (n : ℕ) : Module.finrank ℂ (X n → ℂ) = 3 ^ n := by
  simp

/-- The lane's number: the Schrödinger module of `H(6)` has dimension `729`. -/
theorem finrank_V6 : Module.finrank ℂ (X 6 → ℂ) = 729 := by
  rw [finrank_V]
  norm_num

/-- The trivial action of `H n` on the same space. -/
def trivialAct (_g : H n) (f : X n → ℂ) : X n → ℂ := f

theorem trivialAct_mul (g h : H n) (f : X n → ℂ) :
    trivialAct g (trivialAct h f) = trivialAct (g * h) f := rfl

/-- The trivial action on the same `3ⁿ`-dimensional space is reducible for
`n ≥ 1`: the line spanned by one delta is invariant and proper. -/
theorem trivial_action_reducible (hn : 0 < n) :
    ∃ W : Submodule ℂ (X n → ℂ), InvariantFor trivialAct W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  refine ⟨Submodule.span ℂ {delta (0 : X n)}, fun _ f hf => hf, ?_, ?_⟩
  · intro h
    have hmem : delta (0 : X n) ∈ (⊥ : Submodule ℂ (X n → ℂ)) := by
      rw [← h]; exact Submodule.mem_span_singleton_self _
    rw [Submodule.mem_bot] at hmem
    have := congrFun hmem 0
    simp [delta] at this
  · intro h
    have hne : (e ⟨0, hn⟩ : X n) ≠ 0 := by
      intro hcon
      have := congrFun hcon ⟨0, hn⟩
      simp [e, Pi.single_eq_same] at this
    have hmem : delta (e ⟨0, hn⟩ : X n) ∈ Submodule.span ℂ {delta (0 : X n)} := by
      rw [h]; trivial
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 := congrFun hc (e ⟨0, hn⟩)
    simp [delta, hne, Pi.smul_apply, smul_eq_mul] at h1

/-- **Dimension equality is not representation identity.**  The same
`3ⁿ`-dimensional space carries two actions of the *same* group: the Schrödinger
action, which is irreducible, and the trivial action, which is not.  So a module
of dimension `3ⁿ` — `729` for `n = 6` — is not thereby the Schrödinger module. -/
theorem dimension_is_not_identity (hn : 0 < n) :
    (∀ W : Submodule ℂ (X n → ℂ), InvariantFor T W → W ≠ ⊥ → W = ⊤) ∧
      ∃ W : Submodule ℂ (X n → ℂ), InvariantFor trivialAct W ∧ W ≠ ⊥ ∧ W ≠ ⊤ :=
  ⟨fun _ hW hne => schrodinger_irreducible hW hne, trivial_action_reducible hn⟩

end Integration.Base369Schrodinger
