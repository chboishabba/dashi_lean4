import Integration.TernaryHub

/-!
# The prefix ultrametric on digit addresses, and the codec/369 isometry

`DASHI/Geometry/SSP369Ultrametric.agda` builds, on the carrier
`Address d = Vec Digit369 d`, the agreement depth of two addresses, the distance
`d − agreement`, and an instance of the corpus-wide `Ultrametric` record of
`Ultrametric.agda`.  `DASHI/Codec/TriadicPAdicCodec369Bridge.agda` maps codec
trit kernels into that carrier by `neg ↦ 3, zer ↦ 6, pos ↦ 9` and proves two
things about the map: that it is compatible with inversion, and that the
distance from an address to *itself* is zero.  It does not prove that the map
preserves distances, which is the statement the lane actually needs.

This file develops the geometry once, for an arbitrary finite digit alphabet,
and then instantiates it twice — at `Digit369` and at the balanced-ternary digit
`Trit` — so that the comparison is a theorem rather than a coincidence of
definitions:

* `agree_ge_iff` — the single characterisation lemma (`k ≤ agree x y n` iff the
  two streams agree below `k`) from which symmetry, self-agreement and the
  strong triangle inequality all follow;
* `Addr.ultrametric` — an instance of the corpus's own `AgdaMirror.Ultrametric`
  record, with `Addr.dist_eq_zero_iff` upgrading identity of indiscernibles to a
  biconditional;
* `agree_map` and `Addr.dist_map` — **any injective relabelling of the digit
  alphabet is an isometry**, hence `kernelIsometry`: the corpus's `kernel→369`
  is a distance-preserving bijection from codec kernels onto 3/6/9 addresses,
  and `kernelIsometry_inv` records that it is also polarity-equivariant, so the
  codec lane and the geometry lane are the same metric object.

Boundary: `Addr d α` is a finite set of functions and the distance is a natural
number.  No `p`-adic analysis is claimed; in particular nothing here says the
distance comes from a norm on a ring, and the corpus's own comment that this is
"not an analytic 3-adic norm" is respected.
-/

namespace Integration.Address

open Integration.TernaryHub
open AgdaMirror.DASHIAlgebra (Trit)

variable {α : Type} [DecidableEq α]

/-! ## Agreement depth of two digit streams -/

/-- The length of the common prefix of two streams, truncated at depth `n`.
Faithful to the Agda `agreementDepth`, which recurses on the vector. -/
def agree [DecidableEq α] : (ℕ → α) → (ℕ → α) → ℕ → ℕ
  | _, _, 0 => 0
  | x, y, (n + 1) =>
      if x 0 = y 0 then agree (fun i => x (i + 1)) (fun i => y (i + 1)) n + 1 else 0

@[simp] theorem agree_zero (x y : ℕ → α) : agree x y 0 = 0 := rfl

theorem agree_succ (x y : ℕ → α) (n : ℕ) :
    agree x y (n + 1) =
      if x 0 = y 0 then agree (fun i => x (i + 1)) (fun i => y (i + 1)) n + 1 else 0 := rfl

theorem agree_le (x y : ℕ → α) (n : ℕ) : agree x y n ≤ n := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [agree_succ]
    split
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

/-- The characterisation: the common prefix reaches depth `k` exactly when the
two streams agree at every position below `k`.  Everything else in this file is
a corollary. -/
theorem agree_ge_iff (n : ℕ) : ∀ (k : ℕ) (x y : ℕ → α), k ≤ n →
    (k ≤ agree x y n ↔ ∀ i < k, x i = y i) := by
  induction n with
  | zero =>
    intro k x y hk
    interval_cases k
    simp
  | succ n ih =>
    intro k x y hk
    match k with
    | 0 => simp
    | (k + 1) =>
      rw [agree_succ]
      by_cases h0 : x 0 = y 0
      · rw [if_pos h0]
        rw [Nat.succ_le_succ_iff,
          ih k (fun i => x (i + 1)) (fun i => y (i + 1)) (Nat.le_of_succ_le_succ hk)]
        constructor
        · intro h i hi
          match i with
          | 0 => exact h0
          | (i + 1) => exact h i (Nat.lt_of_succ_lt_succ hi)
        · intro h i hi
          exact h (i + 1) (Nat.succ_lt_succ hi)
      · rw [if_neg h0]
        constructor
        · intro h; exact absurd h (by omega)
        · intro h; exact absurd (h 0 (Nat.succ_pos k)) h0

theorem agree_self (x : ℕ → α) (n : ℕ) : agree x x n = n :=
  Nat.le_antisymm (agree_le x x n) ((agree_ge_iff n n x x le_rfl).2 (fun _ _ => rfl))

theorem agree_symm (x y : ℕ → α) (n : ℕ) : agree x y n = agree y x n := by
  have h : ∀ u v : ℕ → α, agree u v n ≤ agree v u n := by
    intro u v
    exact (agree_ge_iff n _ v u (agree_le u v n)).2
      (fun i hi => ((agree_ge_iff n _ u v (agree_le u v n)).1 le_rfl i hi).symm)
  exact Nat.le_antisymm (h x y) (h y x)

/-- The strong triangle inequality, in the form the Agda states it. -/
theorem agree_triangle (x y z : ℕ → α) (n : ℕ) :
    min (agree x y n) (agree y z n) ≤ agree x z n := by
  have hle : min (agree x y n) (agree y z n) ≤ n :=
    le_trans (min_le_left _ _) (agree_le x y n)
  refine (agree_ge_iff n _ x z hle).2 (fun i hi => ?_)
  have h1 : x i = y i :=
    (agree_ge_iff n _ x y (agree_le x y n)).1 le_rfl i (lt_of_lt_of_le hi (min_le_left _ _))
  have h2 : y i = z i :=
    (agree_ge_iff n _ y z (agree_le y z n)).1 le_rfl i (lt_of_lt_of_le hi (min_le_right _ _))
  exact h1.trans h2

/-- A relabelling of the digit alphabet does not change agreement, provided it is
injective. -/
theorem agree_map {β : Type} [DecidableEq β] (e : α → β) (he : Function.Injective e)
    (x y : ℕ → α) (n : ℕ) :
    agree (fun i => e (x i)) (fun i => e (y i)) n = agree x y n := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [agree_succ, agree_succ]
    by_cases h0 : x 0 = y 0
    · rw [if_pos h0, if_pos (congrArg e h0)]
      exact congrArg (· + 1) (ih _ _)
    · rw [if_neg h0, if_neg (fun h => h0 (he h))]

/-- A *non-injective* relabelling can only increase agreement: coarse-graining
the alphabet is non-expansive. -/
theorem agree_mono_map {β : Type} [DecidableEq β] (f : α → β) (x y : ℕ → α) (n : ℕ) :
    agree x y n ≤ agree (fun i => f (x i)) (fun i => f (y i)) n :=
  (agree_ge_iff n _ _ _ (agree_le x y n)).2
    (fun i hi => congrArg f ((agree_ge_iff n _ x y (agree_le x y n)).1 le_rfl i hi))

/-! ## Finite-depth addresses -/

/-- Depth-`d` addresses over the digit alphabet `α`: the Agda `Address d`. -/
def Addr (d : ℕ) (α : Type) : Type := Fin d → α

instance {d : ℕ} : DecidableEq (Addr d α) := fun _ _ => decidable_of_iff _ funext_iff.symm

/-- An address read as a stream, padded beyond its depth.  The padding is never
inspected: agreement is truncated at the depth. -/
def ext [Inhabited α] {d : ℕ} (a : Addr d α) : ℕ → α :=
  fun i => if h : i < d then a ⟨i, h⟩ else default

namespace Addr

variable [Inhabited α] {d : ℕ}

/-- Agreement depth of two addresses. -/
def agreeA (a b : Addr d α) : ℕ := agree (ext a) (ext b) d

/-- The Agda `distance`: depth minus agreement. -/
def dist (a b : Addr d α) : ℕ := d - agreeA a b

theorem agreeA_le (a b : Addr d α) : agreeA a b ≤ d := agree_le _ _ _

/-- Membership form of the characterisation lemma, stated on the finite carrier. -/
theorem agreeA_ge_iff {k : ℕ} (hk : k ≤ d) (a b : Addr d α) :
    k ≤ agreeA a b ↔ ∀ i : Fin d, (i : ℕ) < k → a i = b i := by
  rw [agreeA, agree_ge_iff d k _ _ hk]
  constructor
  · intro h i hi
    have := h (i : ℕ) hi
    simpa [ext, i.isLt] using this
  · intro h i hi
    have hid : i < d := lt_of_lt_of_le hi hk
    have := h ⟨i, hid⟩ hi
    simpa [ext, hid] using this

@[simp] theorem agreeA_self (a : Addr d α) : agreeA a a = d := agree_self _ _

@[simp] theorem dist_self (a : Addr d α) : dist a a = 0 := by simp [dist]

theorem dist_symm (a b : Addr d α) : dist a b = dist b a := by
  simp [dist, agreeA, agree_symm]

/-- The strong triangle inequality on the finite carrier, in the `max` form of
the corpus's `Ultrametric` record. -/
theorem dist_ultratriangle (a b c : Addr d α) :
    dist a c ≤ max (dist a b) (dist b c) := by
  have h := agree_triangle (ext a) (ext b) (ext c) d
  simp only [dist, agreeA]
  omega

/-- Vanishing distance is equality: the biconditional the Agda proves in one
direction as `distance-zero→equal`. -/
theorem dist_eq_zero_iff (a b : Addr d α) : dist a b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' : d - agreeA a b = 0 := h
    have hd : d ≤ agreeA a b := by omega
    have := (agreeA_ge_iff le_rfl a b).1 hd
    funext i
    exact this i i.isLt
  · rintro rfl; simp

/-- The corpus's `Ultrametric` record, instantiated on depth-`d` addresses. -/
def ultrametric (d : ℕ) (α : Type) [DecidableEq α] [Inhabited α] :
    AgdaMirror.Ultrametric (Addr d α) where
  d := dist
  id_zero := dist_self
  symmetric := dist_symm
  ultratriangle := dist_ultratriangle

@[simp] theorem ultrametric_d (a b : Addr d α) : (ultrametric d α).d a b = dist a b := rfl

/-- Relabelling the alphabet by an injection is an isometry. -/
theorem dist_map {β : Type} [DecidableEq β] [Inhabited β] (e : α ≃ β)
    (a b : Addr d α) :
    dist (fun i => e (a i)) (fun i => e (b i)) = dist a b := by
  have key : ∀ k ≤ d,
      (k ≤ agreeA (fun i => e (a i)) (fun i => e (b i)) ↔ k ≤ agreeA a b) := by
    intro k hk
    rw [agreeA_ge_iff hk, agreeA_ge_iff hk]
    exact ⟨fun h i hi => e.injective (h i hi), fun h i hi => congrArg e (h i hi)⟩
  have h1 := (key _ (agreeA_le a b)).2 le_rfl
  have h2 := (key _ (agreeA_le (fun i => e (a i)) (fun i => e (b i)))).1 le_rfl
  simp only [dist]
  omega

/-- Coarse-graining the alphabet is non-expansive on addresses.  No compatibility
between the two `default`s is needed: agreement is truncated at the depth, so the
padding is never inspected. -/
theorem dist_mono_map {β : Type} [DecidableEq β] [Inhabited β] (f : α → β)
    (a b : Addr d α) :
    dist (fun i => f (a i)) (fun i => f (b i)) ≤ dist a b := by
  have h := (agreeA_ge_iff (agreeA_le a b) a b).1 le_rfl
  have h2 : agreeA a b ≤ agreeA (fun i => f (a i)) (fun i => f (b i)) :=
    (agreeA_ge_iff (agreeA_le a b) _ _).2 (fun i hi => congrArg f (h i hi))
  simp only [dist]
  omega

end Addr

/-! ## The two instantiations: 3/6/9 addresses and codec kernels -/

instance : Inhabited Digit369 := ⟨.d6⟩
instance : Inhabited Trit := ⟨.zer⟩

/-- The Agda `Address d` of `DASHI.Geometry.SSP369Ultrametric`. -/
abbrev Address369 (d : ℕ) := Addr d Digit369

/-- The Agda `Kernel d` of `DASHI.Codec.TriadicPAdicCodec`. -/
abbrev Kernel (d : ℕ) := Addr d Trit

/-- The corpus's `trit→369`, as an equivalence of digit alphabets. -/
def trit369Equiv : Trit ≃ Digit369 where
  toFun := trit369
  invFun := fun d => digitTritTransport.map d
  left_inv := by decide
  right_inv := by decide

/-- The corpus's `kernel→369`, on the finite-depth carriers. -/
def kernelTo369 {d : ℕ} (u : Kernel d) : Address369 d := fun i => trit369 (u i)

/-- **The codec-to-369 map is an isometry.**  The Agda proves only that it sends
an address to distance zero from itself; this is the statement that the codec
lane and the geometry lane carry the same metric. -/
theorem kernelIsometry {d : ℕ} (u v : Kernel d) :
    Addr.dist (kernelTo369 u) (kernelTo369 v) = Addr.dist u v :=
  Addr.dist_map trit369Equiv u v

/-- It is bijective, so the two carriers are the same ultrametric space. -/
def kernelEquiv369 (d : ℕ) : Kernel d ≃ Address369 d :=
  Equiv.arrowCongr (Equiv.refl (Fin d)) trit369Equiv

theorem kernelEquiv369_apply {d : ℕ} (u : Kernel d) : kernelEquiv369 d u = kernelTo369 u := rfl

/-- …and it is polarity-equivariant, which is the one thing the Agda does prove
(`kernel→369-inversion-compatible`), here as a consequence of the digit-level
`trit369_inv` of the ternary hub. -/
theorem kernelIsometry_inv {d : ℕ} (u : Kernel d) :
    kernelTo369 (fun i => Trit.inv (u i)) = fun i => invert369 (kernelTo369 u i) := by
  funext i
  exact trit369_inv (u i)

end Integration.Address
