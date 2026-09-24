import Integration.Address
import Synthesis.Hyperfabric

/-!
# Junction: the Monster 15-prime mask layer *is* the prefix-address geometry

The corpus supplies two ultrametrics that are never compared with each other:

* `DASHI/Algebra/MonsterUltrametric15.agda` (Lean mirror
  `AgdaMirror.MonsterProjection15`) puts the longest-common-prefix distance
  `dMask x y = length x − lcpLen x y` on length-15 boolean *lists*, and
  `Synthesis.MonsterFibre` transports it along `maskFibreEquiv` onto the mask
  fibre `MaskSSP = SSP → Bool` over the fifteen supersingular primes;
* `DASHI/Geometry/SSP369Ultrametric.agda` (developed generically in
  `Integration.Address`) puts the agreement-depth distance on `Addr d α`.

Nothing in the source says these are the same construction — the first recurses
over `List Bool`, the second over an index-indexed stream, and they live in
different files with no import between them.  The main result here is that they
*are* the same:

* `lcpLen_ofFn` — the list-level common-prefix length of `List.ofFn f` and
  `List.ofFn g` is the stream-level agreement depth of `f` and `g`;
* `dSSP_eq_dist` — hence the supplied Monster mask distance is literally the
  depth-15 prefix distance over the two-letter alphabet, and
  `USSP_eq_ultrametric` — the two `Ultrametric` records coincide.

On top of that identification the hyperfabric layer joins in.  A `Fabric` is a
section `SSP → Trit`, i.e. a depth-15 address over the balanced-ternary
alphabet, hence (by `Integration.Address.kernelIsometry`) over the 3/6/9 digit
alphabet:

* `fabricAddrEquiv`, `fabricAddr369Equiv`, `fabric369_isometry`;
* `support_nonexpansive` — the support map `Trit → Bool` of
  `Synthesis.Hyperfabric` is a **non-expansive** map from the ternary fabric
  geometry to the Monster mask geometry.

Honest boundaries, stated as theorems rather than remarks:

* `support_not_isometry` — the non-expansiveness is strict somewhere, so the
  ternary geometry is genuinely finer than the mask geometry;
* `support_not_injective` — the map of carriers is not a bijection, so this is a
  quotient-like collapse, not an equivalence; combined with the supplied
  `Synthesis.Hyperfabric.support_not_hom` (support is not an algebra map), the
  Monster mask layer sits below the ternary layer at classification level (iii)
  plus a one-sided level-(iv) inequality, and no higher.

Nothing here concerns the Monster simple group, moonshine, or vertex operator
algebras: `SSP` is a 15-element enumeration of the supersingular primes and all
statements are about finite functions out of it.
-/

namespace Integration.MonsterFifteen

open Integration.Address
open AgdaMirror.MonsterProjection15 (lcpLen dMask d15 Mask15 UMask15)
open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.DASHIAlgebra (Trit)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric (Fabric support supportMask)

/-! ## `lcpLen` on `List.ofFn` is agreement depth -/

/-- `lcpLen` on a pair of conses, in the branch-free form we need. -/
theorem lcpLen_cons (b c : Bool) (xs ys : List Bool) :
    lcpLen (b :: xs) (c :: ys) = if b = c then lcpLen xs ys + 1 else 0 := by
  cases b <;> cases c <;> simp [lcpLen]

/-- Shifting the padded stream of an address of depth `n + 1` is the padded
stream of its tail. -/
theorem ext_shift {α : Type} [Inhabited α] {n : ℕ} (a : Addr (n + 1) α) :
    (fun i => ext a (i + 1)) = ext (fun i : Fin n => a i.succ) := by
  funext i
  by_cases h : i < n
  · simp [ext, h, Nat.succ_lt_succ h, Fin.succ_mk]
  · simp [ext, h]

/-- **The two common-prefix constructions agree.**  The `List Bool` recursion of
the supplied Monster ultrametric computes exactly the agreement depth of
`Integration.Address`. -/
theorem lcpLen_ofFn : ∀ (n : ℕ) (f g : Addr n Bool),
    lcpLen (List.ofFn f) (List.ofFn g) = agree (ext f) (ext g) n := by
  intro n
  induction n with
  | zero => intro f g; simp
  | succ n ih =>
    intro f g
    rw [List.ofFn_succ, List.ofFn_succ, lcpLen_cons, agree_succ, ext_shift, ext_shift]
    have h0 : ext f 0 = f 0 := by simp [ext]
    have h1 : ext g 0 = g 0 := by simp [ext]
    rw [h0, h1]
    by_cases h : f 0 = g 0
    · rw [if_pos h, if_pos h, ih]
    · rw [if_neg h, if_neg h]

/-- Same statement, packaged on the finite carrier. -/
theorem lcpLen_ofFn_agreeA {n : ℕ} (f g : Addr n Bool) :
    lcpLen (List.ofFn f) (List.ofFn g) = Addr.agreeA f g :=
  lcpLen_ofFn n f g

/-! ## The Monster mask distance is the depth-15 prefix distance -/

/-- The mask fibre read as a depth-15 boolean address. -/
def maskAddr (x : MaskSSP) : Addr 15 Bool := fun i => x (sspEquivFin15.symm i)

/-- The reindexing is an equivalence of carriers. -/
def maskAddrEquiv : MaskSSP ≃ Addr 15 Bool :=
  Equiv.arrowCongr sspEquivFin15 (Equiv.refl Bool)

@[simp] theorem maskAddrEquiv_apply (x : MaskSSP) : maskAddrEquiv x = maskAddr x := rfl

/-- **The supplied Monster mask ultrametric is the prefix ultrametric.** -/
theorem dSSP_eq_dist (x y : MaskSSP) :
    dSSP x y = Addr.dist (maskAddr x) (maskAddr y) := by
  show dMask (List.ofFn (maskAddr x)) (List.ofFn (maskAddr y)) = _
  simp only [dMask, List.length_ofFn, Addr.dist, Addr.agreeA]
  rw [lcpLen_ofFn 15]

/-- …hence the supplied `Ultrametric` record on the Monster mask fibre and the
generic depth-15 prefix `Ultrametric` record carry the same distance function,
which (the fields being propositional) is all the data there is. -/
theorem USSP_d_eq_dist :
    USSP.d = fun x y => Addr.dist (maskAddr x) (maskAddr y) := by
  funext x y; exact dSSP_eq_dist x y

/-- The prefix ultrametric transported to the mask fibre along `maskAddrEquiv`
is the supplied one. -/
theorem USSP_eq_comap :
    USSP.d = (Ultrametric.comap maskAddr (Addr.ultrametric 15 Bool)).d :=
  USSP_d_eq_dist

/-! ## The hyperfabric as a ternary address over the same base -/

/-- A hyperfabric read as a depth-15 balanced-ternary address. -/
def fabricAddr (F : Fabric) : Kernel 15 := fun i => F (sspEquivFin15.symm i)

/-- The reindexing is an equivalence of carriers. -/
def fabricAddrEquiv : Fabric ≃ Kernel 15 :=
  Equiv.arrowCongr sspEquivFin15 (Equiv.refl Trit)

/-- …and, composing with the corpus's `trit→369`, the hyperfabric is a depth-15
3/6/9 address: the Monster base and the ternary geometry lane share one carrier. -/
def fabricAddr369Equiv : Fabric ≃ Address369 15 :=
  fabricAddrEquiv.trans (kernelEquiv369 15)

/-- The ternary distance on hyperfabrics. -/
def fabricDist (F G : Fabric) : ℕ := Addr.dist (fabricAddr F) (fabricAddr G)

/-- The `Ultrametric` record on hyperfabrics. -/
def fabricUltrametric : AgdaMirror.Ultrametric Fabric where
  d := fabricDist
  id_zero := fun F => by simp [fabricDist]
  symmetric := fun F G => Addr.dist_symm _ _
  ultratriangle := fun F G H => Addr.dist_ultratriangle _ _ _

theorem fabricDist_eq_zero_iff (F G : Fabric) : fabricDist F G = 0 ↔ F = G := by
  rw [fabricDist, Addr.dist_eq_zero_iff]
  constructor
  · intro h; exact fabricAddrEquiv.injective h
  · rintro rfl; rfl

/-- **The 3/6/9 relabelling of a hyperfabric is an isometry**, by
`Integration.Address.kernelIsometry`. -/
theorem fabric369_isometry (F G : Fabric) :
    Addr.dist (kernelTo369 (fabricAddr F)) (kernelTo369 (fabricAddr G)) = fabricDist F G :=
  kernelIsometry _ _

/-! ## Support: a non-expansive map onto the Monster mask geometry -/

theorem maskAddr_supportMask (F : Fabric) :
    maskAddr (supportMask F) = fun i => support (fabricAddr F i) := rfl

/-- **The support map is non-expansive** from the ternary hyperfabric geometry to
the supplied Monster mask geometry: coarse-graining the digit alphabet can only
lengthen the common prefix. -/
theorem support_nonexpansive (F G : Fabric) :
    dSSP (supportMask F) (supportMask G) ≤ fabricDist F G := by
  rw [dSSP_eq_dist, maskAddr_supportMask, maskAddr_supportMask]
  exact Addr.dist_mono_map support _ _

/-- **Boundary: not an isometry.**  The inequality is strict for some pair, so
the mask geometry is a genuine coarsening, not a copy, of the ternary geometry. -/
theorem support_not_isometry :
    ¬ ∀ F G : Fabric, dSSP (supportMask F) (supportMask G) = fabricDist F G := by
  intro h
  have := h (fun _ => Trit.zer) (fun _ => Trit.pos)
  rw [dSSP_eq_dist] at this
  have hz : Addr.dist (maskAddr (supportMask (fun _ => Trit.zer)))
      (maskAddr (supportMask (fun _ => Trit.pos))) = 0 := by
    rw [Addr.dist_eq_zero_iff]; rfl
  rw [hz] at this
  have hne : fabricDist (fun _ => Trit.zer) (fun _ => Trit.pos) ≠ 0 := by
    rw [Ne, fabricDist_eq_zero_iff]
    intro hcon
    exact absurd (congrFun hcon SSP.p2) (by decide)
  exact hne this.symm

/-- **Boundary: not injective on carriers.**  The support collapse is two-to-one
on digits, so the Monster mask layer cannot recover the hyperfabric. -/
theorem support_not_injective : ¬ Function.Injective supportMask := by
  intro h
  have : (fun _ => Trit.zer : Fabric) = (fun _ => Trit.pos) := h rfl
  exact absurd (congrFun this SSP.p2) (by decide)

/-- Summary of the junction as a single conjunction: shared carrier (level iii),
a proved one-sided transport of geometry (level iv, inequality only), and two
proved obstructions to upgrading it to an equivalence. -/
theorem monster_ternary_junction :
    (∀ x y : MaskSSP, dSSP x y = Addr.dist (maskAddr x) (maskAddr y)) ∧
      (∀ F G : Fabric, dSSP (supportMask F) (supportMask G) ≤ fabricDist F G) ∧
      ¬ (∀ F G : Fabric, dSSP (supportMask F) (supportMask G) = fabricDist F G) ∧
      ¬ Function.Injective supportMask ∧
      ¬ ∀ a b : Trit, support (AgdaMirror.TritBridge.tritXor a b) = (support a || support b) :=
  ⟨dSSP_eq_dist, support_nonexpansive, support_not_isometry, support_not_injective,
    Synthesis.Hyperfabric.support_not_hom⟩

end Integration.MonsterFifteen
