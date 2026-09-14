import RequestProject.HomotopyTypes

/-!
# Cubical type theory: intervals, cubes, and cubes in a pullback

*Wikidata: cubical type theory (Q139761564), homotopy type theory (Q5891840),
De Morgan algebra (Q5244640), identity type (Q110720714), pullback (Q1397439).*

Cubical type theory replaces the primitive identity type by maps out of an
**interval** with a De Morgan structure: two endpoints, a reversal `1 - i`, and
the connections `i ⊓ j` and `i ⊔ j`.  This file gives the two-point (De Morgan,
in fact Boolean) interval `Ontology.Iv`, defines a **path** in a type as a map
out of it with prescribed endpoints (`Ontology.Path`), and an `n`-**cube** as a
map out of `Iv ^ n` (`Ontology.Cube`), and then asks the question the rest of the
development is about: *what is a cube in a pullback?*

The answer, `Ontology.cubePullbackEquiv`, is the cubical form of the universal
property of `Ontology.pullback`: a cube in the fibre product of two ontologies
is a pair of cubes, one in each, whose images in the reference ontology are
equal cube-by-cube.  It is an instance of `Ontology.mapPullbackEquiv`, which
says the same for maps out of an arbitrary shape — "exponentiation commutes with
pullback".  The one-dimensional case is `Ontology.pathPullbackEquiv`: a path in
the fibre product is a pair of paths that agree over the reference ontology.

Also here: the De Morgan laws of the interval (`Ontology.Iv.deMorgan_meet`,
`Ontology.Iv.deMorgan_join`, `Ontology.Iv.neg_neg`), the equivalence between
reversal of paths (`Ontology.Path.reverse`), and the honest caveat
`Ontology.pathEquivUnit`: a two-point interval made of *points* is indiscrete,
so all the cubical content lies in the cubes and how they meet the pullback.
-/

open CategoryTheory

namespace Wikidata
namespace Ontology

universe u v

/-! ## The interval and its De Morgan structure -/

/-- **The interval** of the cubical reading: two endpoints. -/
abbrev Iv : Type := Bool

namespace Iv

/-- The endpoint `0`. -/
abbrev i0 : Iv := false
/-- The endpoint `1`. -/
abbrev i1 : Iv := true
/-- Reversal `i ↦ 1 - i`. -/
abbrev neg (i : Iv) : Iv := !i
/-- The connection `i ⊓ j`. -/
abbrev meet (i j : Iv) : Iv := i && j
/-- The connection `i ⊔ j`. -/
abbrev join (i j : Iv) : Iv := i || j

@[simp] theorem neg_neg (i : Iv) : neg (neg i) = i := by cases i <;> rfl
@[simp] theorem neg_i0 : neg i0 = i1 := rfl
@[simp] theorem neg_i1 : neg i1 = i0 := rfl

/-- **De Morgan**: the reversal of a meet is the join of the reversals. -/
theorem deMorgan_meet (i j : Iv) : neg (meet i j) = join (neg i) (neg j) := by
  cases i <;> cases j <;> rfl

/-- **De Morgan**: the reversal of a join is the meet of the reversals. -/
theorem deMorgan_join (i j : Iv) : neg (join i j) = meet (neg i) (neg j) := by
  cases i <;> cases j <;> rfl

theorem meet_comm (i j : Iv) : meet i j = meet j i := by cases i <;> cases j <;> rfl
theorem join_comm (i j : Iv) : join i j = join j i := by cases i <;> cases j <;> rfl
theorem meet_idem (i : Iv) : meet i i = i := by cases i <;> rfl
theorem join_idem (i : Iv) : join i i = i := by cases i <;> rfl
theorem meet_i0 (i : Iv) : meet i0 i = i0 := rfl
theorem join_i1 (i : Iv) : join i1 i = i1 := rfl

/-- Wikidata's claim that a De Morgan algebra is a distributive lattice, for the
interval. -/
example : DistribLattice Iv := inferInstance

end Iv

/-! ## Paths and cubes -/

/-- **A path** from `a` to `b`: a map out of the interval with the prescribed
endpoints. -/
def Path {A : Type*} (a b : A) : Type _ := {p : Iv → A // p Iv.i0 = a ∧ p Iv.i1 = b}

/-- The constant path. -/
def Path.refl {A : Type*} (a : A) : Path a a := ⟨fun _ => a, rfl, rfl⟩

/-- **Reversal of a path**, given by the reversal of the interval. -/
def Path.reverse {A : Type*} {a b : A} (p : Path a b) : Path b a := by
  refine ⟨fun i => p.1 (Iv.neg i), ?_, ?_⟩
  · show p.1 Iv.i1 = b
    exact p.2.2
  · show p.1 Iv.i0 = a
    exact p.2.1

/-- **The naive interval identifies everything.** A map out of the two-point
interval is exactly a choice of its two endpoints, so between any two points
there is exactly one path: the two-point set is an *indiscrete* interval.  This
is the reason cubical type theory takes the interval to be a formal object of a
presheaf category rather than a set of points, and it is why the content of the
cubical reading below lies in the *cube functor* `Ontology.Cube` and its
behaviour on the pullback, not in one-dimensional paths. -/
def pathEquivUnit {A : Type*} (a b : A) : Path a b ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨fun i => cond i b a, rfl, rfl⟩
  left_inv p := by
    refine Subtype.ext (funext fun i => ?_)
    cases i
    · exact p.2.1.symm
    · exact p.2.2.symm
  right_inv _ := rfl

instance instSubsingletonPath {A : Type*} (a b : A) : Subsingleton (Path a b) :=
  ⟨fun p q => Subtype.ext (funext fun i => by
    cases i
    · rw [p.2.1, q.2.1]
    · rw [p.2.2, q.2.2])⟩

/-- Reversing a path is an involution. -/
theorem Path.reverse_reverse {A : Type*} {a b : A} (p : Path a b) :
    p.reverse.reverse = p := Subsingleton.elim _ _

/-- **An `n`-cube** in a type: a map out of the `n`-fold product of intervals. -/
def Cube (n : ℕ) (A : Type*) : Type _ := (Fin n → Iv) → A

/-- A `0`-cube is a point. -/
def cubeZeroEquiv (A : Type*) : Cube 0 A ≃ A where
  toFun c := c (fun i => i.elim0)
  invFun a := fun _ => a
  left_inv c := funext fun _ => congrArg c (funext fun i => i.elim0)
  right_inv _ := rfl

/-! ## Cubes in a pullback -/

variable {X Y Z : Ont.{u}}

/-- **Exponentiation commutes with the pullback.** A map from any shape into the
fibre product of two ontologies is a pair of maps, one into each, whose
composites with the two alignments agree. -/
def mapPullbackEquiv (F : X ⟶ Z) (G : Y ⟶ Z) (S : Type v) :
    (S → (pbOnt F G).carrier) ≃
      {q : (S → X.carrier) × (S → Y.carrier) // F.map ∘ q.1 = G.map ∘ q.2} where
  toFun c := ⟨(fun s => (c s).1.1, fun s => (c s).1.2), funext fun s => (c s).2⟩
  invFun q := fun s => ⟨(q.1.1 s, q.1.2 s), congrFun q.2 s⟩
  left_inv c := by
    funext s
    exact Subtype.ext rfl
  right_inv q := by
    refine Subtype.ext ?_
    exact Prod.ext rfl rfl

/-- **A cube in a fibre product is a pair of cubes that agree over the reference
ontology.** -/
def cubePullbackEquiv (F : X ⟶ Z) (G : Y ⟶ Z) (n : ℕ) :
    Cube n (pbOnt F G).carrier ≃
      {q : Cube n X.carrier × Cube n Y.carrier // F.map ∘ q.1 = G.map ∘ q.2} :=
  mapPullbackEquiv F G (Fin n → Iv)

/-- **Naturality in the shape.** Restricting a map along a change of shape acts
componentwise on the pair of maps it corresponds to. -/
theorem mapPullbackEquiv_naturality (F : X ⟶ Z) (G : Y ⟶ Z) {S T : Type v} (f : T → S)
    (c : S → (pbOnt F G).carrier) :
    (mapPullbackEquiv F G T (c ∘ f)).1
      = ((mapPullbackEquiv F G S c).1.1 ∘ f, (mapPullbackEquiv F G S c).1.2 ∘ f) := rfl

/-- The `k`-th face of a cube, at the endpoint `e` of the interval. -/
def Cube.face {A : Type*} {n : ℕ} (k : Fin (n + 1)) (e : Iv) (c : Cube (n + 1) A) : Cube n A :=
  fun v => c (k.insertNth e v)

/-- The degenerate cube in the `k`-th direction. -/
def Cube.degen {A : Type*} {n : ℕ} (k : Fin (n + 1)) (c : Cube n A) : Cube (n + 1) A :=
  fun v => c (fun j => v (k.succAbove j))

/-- **Faces are computed componentwise** in a fibre product: the description of a
cube of the fibre product as a pair of cubes commutes with taking faces. -/
theorem cubePullbackEquiv_face (F : X ⟶ Z) (G : Y ⟶ Z) {n : ℕ} (k : Fin (n + 1)) (e : Iv)
    (c : Cube (n + 1) (pbOnt F G).carrier) :
    (cubePullbackEquiv F G n (Cube.face k e c)).1
      = (Cube.face k e (cubePullbackEquiv F G (n + 1) c).1.1,
         Cube.face k e (cubePullbackEquiv F G (n + 1) c).1.2) := rfl

/-- Likewise for degeneracies. -/
theorem cubePullbackEquiv_degen (F : X ⟶ Z) (G : Y ⟶ Z) {n : ℕ} (k : Fin (n + 1))
    (c : Cube n (pbOnt F G).carrier) :
    (cubePullbackEquiv F G (n + 1) (Cube.degen k c)).1
      = (Cube.degen k (cubePullbackEquiv F G n c).1.1,
         Cube.degen k (cubePullbackEquiv F G n c).1.2) := rfl

/-- **A path in a fibre product is a pair of paths that agree over the reference
ontology.** -/
def pathPullbackEquiv (F : X ⟶ Z) (G : Y ⟶ Z) (p q : (pbOnt F G).carrier) :
    Path p q ≃ {r : Path p.1.1 q.1.1 × Path p.1.2 q.1.2 //
      ∀ i, F.map (r.1.1 i) = G.map (r.2.1 i)} where
  toFun c :=
    ⟨(⟨fun i => (c.1 i).1.1, congrArg (fun t => t.1.1) c.2.1, congrArg (fun t => t.1.1) c.2.2⟩,
      ⟨fun i => (c.1 i).1.2, congrArg (fun t => t.1.2) c.2.1, congrArg (fun t => t.1.2) c.2.2⟩),
      fun i => (c.1 i).2⟩
  invFun r :=
    ⟨fun i => ⟨(r.1.1.1 i, r.1.2.1 i), r.2 i⟩,
      Subtype.ext (Prod.ext r.1.1.2.1 r.1.2.2.1),
      Subtype.ext (Prod.ext r.1.1.2.2 r.1.2.2.2)⟩
  left_inv c := by
    refine Subtype.ext (funext fun i => Subtype.ext (Prod.ext rfl rfl))
  right_inv r := by
    refine Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))

/-- Two matched pairs are equal exactly when their components are: the identity
type of the fibre product is the product of the identity types, over the
reference ontology. -/
theorem pullback_eq_iff (F : X ⟶ Z) (G : Y ⟶ Z) (p q : (pbOnt F G).carrier) :
    p = q ↔ p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 h2)

end Ontology
end Wikidata
