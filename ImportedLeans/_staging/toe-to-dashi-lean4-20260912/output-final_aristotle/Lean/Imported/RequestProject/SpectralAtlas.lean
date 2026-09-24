import RequestProject.Anatomy
import RequestProject.MoonshineAddress

/-!
# SpectralAtlas: the multihash / graded moonshine projection

The earlier `MoonshineAddress` layer drives the whole 20 176-dimensional embedding
from a **single scalar hash** `h : ℕ`:

```
  ℕ  ─Stage1─▶  ℤ¹⁵  ─Stage2─▶  ℤ¹⁹⁴  ─Stage3─▶  ℤ^(194×104)
```

This module realises the *spectral* refinement discussed for the atlas: instead of
one integer, an object is viewed as a **multihash**

  `μ : Fin 15 → ℕ`

— one channel per Monster prime — and each of the 194 irreps becomes a *distinct
lens* reading its own channel `μ (i % 15)`.  The q-expansion then composes these
lenses into graded spectral channels.  Concretely:

* `MultiHash`        — the source object: a 15-channel structural fingerprint.
* `irrepWeightV`     — irrep `i` reads channel `i % 15` (the "lens").
* `gradedCoord`      — irrep `i`, q-page `k` coordinate.
* `gradedPoint μ N`  — the **grade-`N` jet**: the embedding truncated to the first
  `N` q-pages.  `gradedPoint μ numPages` is the full embedding.

## AST-driven multihash

The 12 `Expr` constructors of `Anatomy.LangProfile`, together with `size`, `depth`
and `consts`, give exactly **15** structural invariants — one per Monster prime.
`langMultiHash` packages them so that *constructor counts, AST depth and constant
usage* drive the moonshine embedding, rather than a single opaque hash.  The
`#spectral f` command prints this AST-driven multihash address.

## Graded jets: compatibility, privacy, separation

The grading behaves like the truncation of a holomorphic q-expansion to a finite
jet:

* `gradedPoint_prefix`      — a higher grade *restricts* to every lower grade: the
  grades form a compatible tower (a higher-resolution view refines a coarser one).
* `fullPoint_scalar`        — on a constant multihash the spectral pipeline
  *reduces exactly* to the original scalar `MoonshineAddress.moonshinePoint`, so
  this layer strictly generalises the previous one.
* `grade_zero_uninformative`— the grade-`0` jet is the empty observation: it is the
  *same* for every object (maximal privacy / total information loss).
* `grade_zero_collision_separated` — two objects can share the (trivial) grade-`0`
  jet yet already separate once a single q-page is revealed: revealing more grades
  reveals more structure (a lossy → faithful hierarchy).
* `spectral_separation_local` / `spectral_separation` — the faithfulness result:
  multihashes that differ in their prime channels land at different coordinates.
-/

namespace SpectralAtlas

open Moonshine MoonshineAddress

/-! ## The multihash source object -/

/-- A **multihash**: a 15-channel structural fingerprint, one channel per Monster
prime.  This replaces the single scalar hash of `MoonshineAddress` — each Monster
irrep will read its own channel as an independent "lens" on the object. -/
abbrev MultiHash := Fin 15 → Nat

/-! ## Stage 2 (spectral): each irrep is a distinct channel lens -/

/-- The weight of irrep `i` for multihash `μ`.

Irrep `i` is tuned to Monster prime `mp (i % 15)` and reads **its own channel**
`μ (i % 15)`:

  `irrepWeightV μ i = irrepScale i · (μ (i % 15) mod mp (i % 15))`.

This is the multihash analogue of `MoonshineAddress.irrepWeight`, where the single
hash `h` is replaced by the per-prime channel `μ (i % 15)`. -/
def irrepWeightV (μ : MultiHash) (i : Fin 194) : Int :=
  irrepScale i * Int.ofNat (μ (primeOf i) % mp (primeOf i))

/-! ## Stage 3 (spectral): graded q-expansion jets -/

/-- The moonshine coordinate of multihash `μ` at irrep `i` and q-page `k`:

  `gradedCoord μ i k = irrepWeightV μ i · jCoeff (k + 2)`. -/
def gradedCoord (μ : MultiHash) (i : Fin 194) (k : Nat) : Int :=
  irrepWeightV μ i * jCoeff (k + 2)

/-- The **grade-`grade` jet**: the moonshine embedding of `μ` truncated to the
first `grade` q-pages, living in `ℤ^(194 × grade)`.  Increasing `grade` reveals
finer holomorphic detail (more q-coefficients). -/
def gradedPoint (μ : MultiHash) (grade : Nat) : Fin 194 × Fin grade → Int :=
  fun p => gradedCoord μ p.1 p.2.val

/-- The full (maximal-grade) moonshine point in `ℤ^(194×104) = ℤ^20176`. -/
def fullPoint (μ : MultiHash) : Fin 194 × Fin numPages → Int :=
  gradedPoint μ numPages

/-! ## Compatibility of the grading tower -/

/-- **Grade tower compatibility.**  For `N ≤ M`, the grade-`M` jet *restricts* to
the grade-`N` jet: looking at the first `N` pages of the higher-resolution view
gives exactly the lower-resolution view.  The graded embeddings form a compatible
tower of progressively finer (more reconstructive) approximations. -/
theorem gradedPoint_prefix (μ : MultiHash) {N M : Nat} (hNM : N ≤ M)
    (i : Fin 194) (k : Fin N) :
    gradedPoint μ M (i, ⟨k.val, Nat.lt_of_lt_of_le k.isLt hNM⟩) = gradedPoint μ N (i, k) :=
  rfl

/-! ## Reduction to the scalar pipeline -/

/-- On a **constant** multihash `μ = fun _ => h`, irrep weights coincide with the
original scalar `MoonshineAddress.irrepWeight h`. -/
theorem irrepWeightV_const (h : Nat) (i : Fin 194) :
    irrepWeightV (fun _ => h) i = MoonshineAddress.irrepWeight h i :=
  rfl

/-- On a constant multihash the full spectral embedding **reduces exactly** to the
scalar `MoonshineAddress.moonshinePoint`.  Hence the spectral atlas strictly
generalises the previous hash atlas (it is recovered by the diagonal embedding
`h ↦ fun _ => h`). -/
theorem fullPoint_scalar (h : Nat) (p : Fin 194 × Fin numPages) :
    fullPoint (fun _ => h) p = MoonshineAddress.moonshinePoint h p :=
  rfl

/-! ## Privacy: the grade-0 jet is uninformative -/

/-- **Maximal privacy at grade 0.**  The grade-`0` jet exposes *nothing*: it is the
same (empty) observation for every object.  This is the coarsest, most
privacy-preserving view in the tower. -/
theorem grade_zero_uninformative (μ ν : MultiHash) :
    gradedPoint μ 0 = gradedPoint ν 0 := by
  funext p
  exact p.2.elim0

/-! ## Faithfulness / separation -/

/-- **Prime-local spectral separation.**  If multihashes `μ`, `ν` differ in the
channel of Monster prime `mp j` (modulo that prime), then at every irrep `i` tuned
to `j` and every q-page `k`, their graded coordinates differ. -/
theorem spectral_separation_local
    (μ ν : MultiHash) (j : Fin 15)
    (i : Fin 194) (hi : i.val % 15 = j.val)
    (k : Fin numPages)
    (hdiff : μ j % mp j ≠ ν j % mp j) :
    gradedCoord μ i k.val ≠ gradedCoord ν i k.val := by
  intro heq
  have hpg := MoonshineAddress.jCoeffPage_ne_zero k
  have hirr : irrepWeightV μ i = irrepWeightV ν i := mul_right_cancel₀ hpg heq
  have hsc := MoonshineAddress.irrepScale_ne_zero i
  have haddr : Int.ofNat (μ (primeOf i) % mp (primeOf i))
      = Int.ofNat (ν (primeOf i) % mp (primeOf i)) :=
    mul_left_cancel₀ hsc hirr
  have hpj : primeOf i = j := Fin.ext hi
  rw [hpj] at haddr
  exact hdiff (Int.ofNat.inj haddr)

/-- **Spectral separation.**  If `μ` and `ν` differ in *every* prime channel, then
already at grade 1 (irrep 0, page 0) they occupy different moonshine coordinates:
distinct multihashes are faithfully separated. -/
theorem spectral_separation
    (μ ν : MultiHash)
    (hdiff : ∀ j : Fin 15, μ j % mp j ≠ ν j % mp j) :
    gradedCoord μ ⟨0, by decide⟩ 0 ≠ gradedCoord ν ⟨0, by decide⟩ 0 :=
  spectral_separation_local μ ν ⟨0, by decide⟩ ⟨0, by decide⟩ rfl ⟨0, by decide⟩
    (hdiff ⟨0, by decide⟩)

/-- **Lossy → faithful hierarchy.**  Two objects can share the (trivial) grade-`0`
jet — total privacy — and yet already separate the moment a single q-page is
revealed.  Concretely `μ ≡ 0` and `ν ≡ 1` collide at grade 0 but differ at the very
first graded coordinate. -/
theorem grade_zero_collision_separated :
    ∃ μ ν : MultiHash,
      gradedPoint μ 0 = gradedPoint ν 0 ∧
      gradedCoord μ ⟨0, by decide⟩ 0 ≠ gradedCoord ν ⟨0, by decide⟩ 0 :=
  ⟨(fun _ => 0), (fun _ => 1), grade_zero_uninformative _ _, by native_decide⟩

/-! ## Dimension -/

/-- The full grading lands in `ℤ^(194×104) = ℤ^20176`. -/
theorem fullPoint_dimension : 194 * numPages = 20176 := by native_decide

/-! ## AST-driven multihash (Anatomy → SpectralAtlas) -/

open Anatomy

/-- The 15 structural channels extracted from an AST profile: the 12 `Expr`
constructor counts (in `Kind.all` order), followed by `size`, `depth`, `consts`.
Exactly 15 invariants — one per Monster prime. -/
def langChannels (p : LangProfile) : Array Nat :=
  ((p.counts.map (·.2)) ++ [p.size, p.depth, p.consts]).toArray

/-- The AST-driven multihash of a language profile: structural invariants
(constructor histogram, depth, constant usage) drive the moonshine embedding,
replacing the single opaque declaration hash. -/
def langMultiHash (p : LangProfile) : MultiHash :=
  fun j => (langChannels p).getD j.val 0

/-! ## Reflection command -/

open Lean Meta Elab Command

/-- Render the 15 prime-channel residues `μ_j mod p_j` of a multihash. -/
def residueLine (μ : MultiHash) : String :=
  String.intercalate "  "
    ((List.finRange 15).map (fun j => s!"{mp j}:{μ j % mp j}"))

/-- `#spectral f` reflects `f` into its AST profile, builds the AST-driven
multihash, and prints its spectral moonshine address: the 15 prime-channel
residues and the first graded coordinates of irrep 0. -/
syntax (name := spectralCmd) "#spectral " ident : command

@[command_elab spectralCmd]
def elabSpectral : CommandElab := fun stx => do
  match stx with
  | `(#spectral $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let p ← liftTermElabM <| Meta.MetaM.run' (Anatomy.analyzeDecl name)
    let μ := langMultiHash p
    let c00 := gradedCoord μ ⟨0, by decide⟩ 0
    let c01 := gradedCoord μ ⟨0, by decide⟩ 1
    logInfo s!"[Spectral Atlas] {name}\n  AST-driven multihash:  size={p.size}  depth={p.depth}  consts={p.consts}  language={p.features}/12\n  15 prime-channel residues (μ_j mod p_j):\n    {residueLine μ}\n  graded coords ⟨irrep 0⟩:  page0={c00}  page1={c01}\n  full grading: 194 × {numPages} = {194 * numPages} dims"
  | _ => throwError "ill-formed #spectral command"

/-! ## Test suite -/

#spectral Nat.add
#spectral List.map
#spectral Prod.fst

end SpectralAtlas
