import Mathlib
import RequestProject.GF27
import RequestProject.KernelReflection

/-!
# `RetractiveCore` — the shared idempotent-fixed-point structure

This is the user-supplied `RetractiveCore.lean` draft, reworked so that it compiles, contains
no `axiom` declarations and no `sorry`, and so that its two "hooks" are *discharged by real
kernel computations* rather than assumed.

What is kept from the draft:

* `RetractiveCore.Bootstrap` : the abstract structure `(compile : Bin → Src → Bin, seed, self)`.
* `Bootstrap.stage`, `Bootstrap.IsCorrect`, `Bootstrap.stage_eq_of_correct_one`,
  `Bootstrap.stage_two_eq_stage_three`, `Bootstrap.correct_fixed_point_unique` : proved, once,
  abstractly.

What is changed, and why:

* The draft introduced `axiom GCCBin`, `axiom gccCompile`, `axiom gcc_stage_one_correct`, and the
  same for Lean's stage0/stage1/stage2 build.  Adding `axiom`s is not sound practice: an
  `axiom` is an unchecked assumption, and `gcc_stage_one_correct` / `lean_stage_one_correct`
  are empirical claims about build artefacts, not theorems.  They are therefore **not**
  declared here; the original text is retained verbatim, commented out, at the bottom of this
  file.  Instead, `Bootstrap` is instantiated over *arbitrary* data
  (`selfHosting_stage_two_eq_stage_three`), with "stage 1 is correct" as an explicit
  hypothesis.  Instantiating that hypothesis with a real build comparison is exactly the hook
  the draft wanted, and it is available without assuming anything.

* The draft's closing note is right that Lean *kernel reduction* is not compiler self-hosting.
  The genuine mathematical content shared by the draft's `Bootstrap` and by the retractions of
  `RequestProject/Frobenius.lean` and `RequestProject/CenterRetraction.lean` is isolated here as
  `RetractiveCore.IsIdempotent`: an idempotent self-map is precisely a retraction onto its
  image, and its image is its fixed-point set (`range_eq_fixedPoints`, `restrict_id`).

* Two *honest, axiom-free* instances of `Bootstrap` are then given, whose "stage 1 is correct"
  premise is a fact **verified by the Lean 4 kernel** (`decide +kernel`), not an assumption:
  `gf27Bootstrap`, built from the Frobenius orbit product `x ↦ x ^ 13` on `GF27`, and
  `centerBootstrap`, built from the retraction of `D₃ × C₂` onto its center.  These are the
  sense in which "the retraction is reached in the Lean 4 kernel via reflection".
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace RetractiveCore

/-! ### The abstract structure (from the draft) -/

/-- Abstract shape of a self-hosting compiler bootstrap.
    `Bin`  : the space of binaries / executable artifacts
    `Src`  : the space of source texts
    `compile b s` : compile source `s` using binary `b`, producing a new binary
    `seed` : the initial (stage-0) binary
    `self` : the compiler's own source code -/
structure Bootstrap (Bin Src : Type*) where
  compile : Bin → Src → Bin
  seed : Bin
  self : Src

namespace Bootstrap

variable {Bin Src : Type*} (B : Bootstrap Bin Src)

/-- The n-th stage binary: stage 0 is the seed, stage (n+1) is `self` compiled by stage n. -/
def stage : ℕ → Bin
  | 0 => B.seed
  | n + 1 => B.compile (stage n) B.self

@[simp] theorem stage_zero : B.stage 0 = B.seed := rfl

@[simp] theorem stage_succ' (n : ℕ) : B.stage (n + 1) = B.compile (B.stage n) B.self := by
  simp [stage]

/-- A binary `b` is a correct compiler for `self` iff compiling `self` with `b` reproduces `b`. -/
def IsCorrect (b : Bin) : Prop := B.compile b B.self = b

/-- If some stage `n` is already correct, every later stage equals it. -/
theorem stage_eq_of_correct_one {n : ℕ} (h : B.IsCorrect (B.stage n)) :
    ∀ k, B.stage (n + k) = B.stage n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show B.stage (n + k + 1) = B.stage n
      rw [stage_succ', ih]
      exact h

/-- Corollary: if stage 1 is correct, stage 2 = stage 3 (the concrete three-stage bootstrap
comparison a self-hosting build system actually performs). -/
theorem stage_two_eq_stage_three (h : B.IsCorrect (B.stage 1)) :
    B.stage 2 = B.stage 3 := by
  have h2 : B.stage (1 + 1) = B.stage 1 := stage_eq_of_correct_one B h 1
  have h3 : B.stage (1 + 2) = B.stage 1 := stage_eq_of_correct_one B h 2
  have : (1 + 1 : ℕ) = 2 := rfl
  have h' : (1 + 2 : ℕ) = 3 := rfl
  rw [this] at h2
  rw [h'] at h3
  rw [h2, h3]

/-- Uniqueness: any two correct stages of the same run coincide.

(The draft also assumed `hn : B.IsCorrect (B.stage n)`; it is not needed — correctness of the
earlier stage already forces the later one to agree with it — so it is omitted here.) -/
theorem correct_fixed_point_unique {m n : ℕ}
    (hm : B.IsCorrect (B.stage m)) (hmn : m ≤ n) : B.stage m = B.stage n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  exact (stage_eq_of_correct_one B hm k).symm

/-- The one-step compile action `b ↦ compile b self`, whose fixed points are the correct
binaries. -/
def step (b : Bin) : Bin := B.compile b B.self

theorem isCorrect_iff_step_eq (b : Bin) : B.IsCorrect b ↔ B.step b = b := Iff.rfl

theorem stage_succ (n : ℕ) : B.stage (n + 1) = B.step (B.stage n) := by simp [step]

end Bootstrap

/-! ### The retractive core: idempotent self-maps are retractions onto their fixed points

This is the structure genuinely shared by the draft's `Bootstrap`, by the Frobenius orbit
product of `RequestProject/Frobenius.lean`, and by a retraction onto the center of a group. -/

/-- `f` is idempotent: applying it twice is the same as applying it once. -/
def IsIdempotent {α : Type*} (f : α → α) : Prop := ∀ a, f (f a) = f a

namespace IsIdempotent

variable {α : Type*} {f : α → α}

/-- The image of an idempotent map is its set of fixed points. -/
theorem range_eq_fixedPoints (hf : IsIdempotent f) :
    Set.range f = {a | f a = a} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact hf b
  · intro ha
    exact ⟨a, ha⟩

/-- An idempotent map restricts to the identity on its image: it is a *retraction* of `α` onto
`Set.range f`. -/
theorem restrict_id (hf : IsIdempotent f) {a : α} (ha : a ∈ Set.range f) : f a = a := by
  rw [hf.range_eq_fixedPoints] at ha
  exact ha

/-- Every point is carried into the image, which is where it stays. -/
theorem apply_mem_range (f : α → α) (a : α) : f a ∈ Set.range f := ⟨a, rfl⟩

end IsIdempotent

/-- For a bootstrap whose compile action is idempotent, the correct binaries are exactly the
reachable ones, stage 1 is already correct, and the build stabilises from stage 1 on. -/
theorem Bootstrap.stage_one_correct_of_idempotent {Bin Src : Type*} (B : Bootstrap Bin Src)
    (h : IsIdempotent B.step) : B.IsCorrect (B.stage 1) := by
  rw [B.isCorrect_iff_step_eq, B.stage_succ 0]
  exact h (B.stage 0)

/-! ### Instance: an arbitrary self-hosting build (the draft's GCC / Lean 4 hook)

No `axiom`s: the data of a bootstrap and the empirical fact "stage 1 is correct" are taken as
parameters.  Supplying real build artefacts for `compile`, `seed`, `self` and a real
stage1 = stage2 comparison for `h` yields the concrete statement the draft wanted, for GCC's
`make bootstrap` or for Lean's stage0 → stage1 → stage2 build alike. -/

section SelfHosting

variable {Bin Src : Type*} (compile : Bin → Src → Bin) (seed : Bin) (self : Src)

/-- The bootstrap determined by a compile action, a seed binary and the compiler's own source. -/
def selfHostingBootstrap : Bootstrap Bin Src :=
  { compile := compile, seed := seed, self := self }

/-- The draft's `gcc_stage_two_eq_three` and `lean_stage_two_eq_three`, as a single theorem
about arbitrary build data: if stage 1 is a correct compiler for `self`, then stage 2 and
stage 3 agree. -/
theorem selfHosting_stage_two_eq_stage_three
    (h : (selfHostingBootstrap compile seed self).IsCorrect
      ((selfHostingBootstrap compile seed self).stage 1)) :
    (selfHostingBootstrap compile seed self).stage 2 =
      (selfHostingBootstrap compile seed self).stage 3 :=
  Bootstrap.stage_two_eq_stage_three _ h

end SelfHosting

/-! ### Instance: the Frobenius retraction on `GF27`, verified by the Lean 4 kernel -/

namespace GF27Instance

open GF27

/-- Kernel check: the Frobenius orbit product `x ↦ x ^ 13` on `GF27` is idempotent. -/
def normIdempotentCheck : Bool := enum.all fun x => pow' (pow' x 13) 13 == pow' x 13

theorem normIdempotentCheck_eq_true : normIdempotentCheck = true := by decide +kernel

/-- The orbit product `x ↦ x ^ 13` of `RequestProject/Frobenius.lean`, at `p = 3`, `n = 3`,
is idempotent — verified by kernel computation. -/
theorem isIdempotent_norm : IsIdempotent (fun x : GF27 => x ^ 13) := by
  intro x
  have h := KernelReflection.reflect_forall mem_enum normIdempotentCheck_eq_true x
  simpa [pow'_eq] using h

/-- The image of the orbit product is exactly the prime subfield `𝔽₃ = {0, 1, 2}`, and the
orbit product is a retraction of `GF27` onto it. -/
theorem range_norm_eq_primeSubfield :
    Set.range (fun x : GF27 => x ^ 13) = ({0, 1, 2} : Set GF27) := by
  rw [isIdempotent_norm.range_eq_fixedPoints]
  ext x
  constructor
  · intro hx
    have := norm_mem_prime x
    rw [Set.mem_setOf_eq] at hx
    rw [hx] at this
    simpa using this
  · intro hx
    exact norm_fixes_prime (by simpa using hx)

/-- The Frobenius orbit product on `GF27`, packaged as an instance of the draft's `Bootstrap`
structure: the "binaries" are field elements, the "source" is trivial, and "compiling" is one
application of the orbit product. -/
def gf27Bootstrap : Bootstrap GF27 Unit :=
  { compile := fun x _ => x ^ 13, seed := ⟨1, 1, 0⟩, self := () }

theorem gf27_step (x : GF27) : gf27Bootstrap.step x = x ^ 13 := rfl

/-- **The draft's hook, discharged by the kernel instead of assumed.**
Where the draft wrote `axiom gcc_stage_one_correct`, here the corresponding fact is a theorem:
stage 1 of `gf27Bootstrap` is correct, because the kernel computes that `x ^ 13` is a fixed
point of `x ↦ x ^ 13`. -/
theorem gf27_stage_one_correct : gf27Bootstrap.IsCorrect (gf27Bootstrap.stage 1) :=
  Bootstrap.stage_one_correct_of_idempotent gf27Bootstrap (fun x => isIdempotent_norm x)

/-- Consequently the abstract three-stage theorem applies, with no assumptions at all. -/
theorem gf27_stage_two_eq_three : gf27Bootstrap.stage 2 = gf27Bootstrap.stage 3 :=
  Bootstrap.stage_two_eq_stage_three _ gf27_stage_one_correct

end GF27Instance

/-! ### Instance: the retraction onto the center of `D₃ × C₂`, verified by the Lean 4 kernel -/

namespace CenterInstance

open DihedralProd

/-- Kernel check: the map `(d, c) ↦ (1, c)` on `D₃ × C₂` is idempotent. -/
theorem isIdempotent_r : IsIdempotent (r : G → G) := by
  intro g
  revert g
  decide +kernel

/-- The center retraction of `D₃ × C₂`, as an instance of the draft's `Bootstrap` structure. -/
def centerBootstrap : Bootstrap G Unit :=
  { compile := fun g _ => r g, seed := (DihedralGroup.r 1, Multiplicative.ofAdd 1), self := () }

/-- Again the "stage 1 is correct" hook is a kernel-verified theorem, not an axiom. -/
theorem center_stage_one_correct : centerBootstrap.IsCorrect (centerBootstrap.stage 1) :=
  Bootstrap.stage_one_correct_of_idempotent centerBootstrap (fun g => isIdempotent_r g)

theorem center_stage_two_eq_three : centerBootstrap.stage 2 = centerBootstrap.stage 3 :=
  Bootstrap.stage_two_eq_stage_three _ center_stage_one_correct

/-- The image of the retraction is the center of `D₃ × C₂`, and the retraction is the identity
on it — the group-theoretic instance of `IsIdempotent.range_eq_fixedPoints`. -/
theorem range_r_eq_center :
    Set.range (r : G → G) = {g : G | g ∈ Subgroup.center G} := by
  rw [isIdempotent_r.range_eq_fixedPoints]
  ext g
  constructor
  · intro hg
    rw [Set.mem_setOf_eq] at hg
    rw [Set.mem_setOf_eq, Subgroup.mem_center_iff]
    intro h
    have := r_mem_center_check g h
    rwa [hg] at this
  · intro hg
    exact r_fix_check g fun h => Subgroup.mem_center_iff.1 hg h

end CenterInstance

end RetractiveCore

/-
### The original draft, retained verbatim

The declarations below are the `axiom`-based parts of the submitted `RetractiveCore.lean`.
They are kept commented out rather than deleted: `axiom` declarations are unchecked
assumptions, and the two build-artefact facts (`gcc_stage_one_correct`,
`lean_stage_one_correct`) are empirical, not mathematical.  Everything they were used for is
provided above either parametrically (`selfHosting_stage_two_eq_stage_three`) or with the
hypothesis actually proved by kernel computation (`gf27_stage_one_correct`,
`center_stage_one_correct`).

section GCC

axiom GCCBin  : Type
axiom GCCSrc  : Type
axiom gccCompile : GCCBin → GCCSrc → GCCBin
axiom gccSeed    : GCCBin      -- e.g. a bootstrap C compiler (stage-0)
axiom gccSelf    : GCCSrc      -- GCC's own source tree

def gccBootstrap : Bootstrap.{0} GCCBin GCCSrc :=
  { compile := gccCompile, seed := gccSeed, self := gccSelf }

axiom gcc_stage_one_correct : gccBootstrap.IsCorrect (gccBootstrap.stage 1)

theorem gcc_stage_two_eq_three : gccBootstrap.stage 2 = gccBootstrap.stage 3 :=
  Bootstrap.stage_two_eq_stage_three gccBootstrap gcc_stage_one_correct

end GCC

section Lean4

axiom LeanBin : Type
axiom LeanSrc : Type
axiom leanCompile : LeanBin → LeanSrc → LeanBin
axiom leanStage0   : LeanBin   -- pinned prior-release binary
axiom leanSelf     : LeanSrc   -- Lean compiler's own source (src/)

def leanBootstrap : Bootstrap.{0} LeanBin LeanSrc :=
  { compile := leanCompile, seed := leanStage0, self := leanSelf }

axiom lean_stage_one_correct : leanBootstrap.IsCorrect (leanBootstrap.stage 1)

theorem lean_stage_two_eq_three : leanBootstrap.stage 2 = leanBootstrap.stage 3 :=
  Bootstrap.stage_two_eq_stage_three leanBootstrap lean_stage_one_correct

end Lean4
-/
