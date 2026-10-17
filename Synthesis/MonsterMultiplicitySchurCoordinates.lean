import Mathlib

/-!
# Schur-coordinate compiler for Monster-style multiplicity spaces

This is a representation-independent post-recognition theorem.  Once an actual
simple module `H` has been recognized and an actual sector has already been
identified with `n` diagonal copies of `H`, a proof-relevant Schur certificate
(`End_G(H)` consists exactly of scalar maps) forces the equivariant Hom space
`Hom_G(H,H^n)` to have exactly `n` scalar coordinates.

The theorem deliberately starts *after* same-object/isotypic recognition.  It
does not construct the Monster `W_zeta` attachment, a Suzuki/normalizer action,
zeta orientation, or the tensor evaluation equivalence `H tensor S -> W`.
Those remain separate actual-representation obligations.
-/

namespace Synthesis.MonsterMultiplicitySchurCoordinates

noncomputable section

universe u

variable {k G V W : Type u}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- Minimal linear group-action surface used by this compiler. -/
structure Representation (G k V : Type u)
    [Group G] [Field k] [AddCommGroup V] [Module k V] where
  act : G -> V ->ₗ[k] V
  one_act : ∀ x, act 1 x = x
  mul_act : ∀ g h x, act (g * h) x = act g (act h x)

/-- Linear intertwiners between two actions on the same group/scalar field. -/
structure EquivariantHom
    (A : Representation G k V) (B : Representation G k W) where
  toLinearMap : V ->ₗ[k] W
  intertwines : ∀ g x, B.act g (toLinearMap x) = toLinearMap (A.act g x)

@[ext]
theorem EquivariantHom.ext
    {A : Representation G k V} {B : Representation G k W}
    {f g : EquivariantHom A B}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Diagonal action on `n` copies of one representation. -/
def piRepresentation (A : Representation G k V) (n : ℕ) :
    Representation G k (Fin n -> V) where
  act g :=
    { toFun := fun x i => A.act g (x i)
      map_add' := by
        intro x y
        funext i
        exact (A.act g).map_add (x i) (y i)
      map_smul' := by
        intro c x
        funext i
        exact (A.act g).map_smul c (x i) }
  one_act := by
    intro x
    funext i
    exact A.one_act (x i)
  mul_act := by
    intro g h x
    funext i
    exact A.mul_act g h (x i)

/-- Scalar endomorphisms are always equivariant. -/
def scalarEndo (A : Representation G k V) (a : k) : EquivariantHom A A where
  toLinearMap :=
    { toFun := fun x => a • x
      map_add' := by intro x y; simp [smul_add]
      map_smul' := by intro c x; simp [smul_smul, mul_comm] }
  intertwines := by
    intro g x
    simpa using (A.act g).map_smul a x

/-- Proof-relevant Schur input.  The actual Monster consumer must obtain this
for the same recognized simple `H_zeta`; it is not inferred from dimension or a
character label. -/
structure SchurScalarCertificate (A : Representation G k V) where
  scalarOf : EquivariantHom A A -> k
  scalar_spec : ∀ f x, f.toLinearMap x = scalarOf f • x
  scalarOf_scalarEndo : ∀ a, scalarOf (scalarEndo A a) = a

/-- One coordinate of an intertwiner into a diagonal finite-copy action. -/
def coordinateHom
    (A : Representation G k V) {n : ℕ}
    (f : EquivariantHom A (piRepresentation A n)) (i : Fin n) :
    EquivariantHom A A where
  toLinearMap :=
    { toFun := fun x => f.toLinearMap x i
      map_add' := by
        intro x y
        exact congrFun (f.toLinearMap.map_add x y) i
      map_smul' := by
        intro c x
        exact congrFun (f.toLinearMap.map_smul c x) i }
  intertwines := by
    intro g x
    simpa [piRepresentation] using congrFun (f.intertwines g x) i

/-- Build an equivariant map into `n` copies from `n` scalar coefficients. -/
def scalarsToHom
    (A : Representation G k V) {n : ℕ} (a : Fin n -> k) :
    EquivariantHom A (piRepresentation A n) where
  toLinearMap :=
    { toFun := fun x i => a i • x
      map_add' := by
        intro x y
        funext i
        simp [smul_add]
      map_smul' := by
        intro c x
        funext i
        simp [smul_smul, mul_comm] }
  intertwines := by
    intro g x
    funext i
    simpa [piRepresentation] using (A.act g).map_smul (a i) x

/-- Read scalar coordinates from an equivariant map by Schur's lemma. -/
def homToScalars
    (A : Representation G k V) (cert : SchurScalarCertificate A) {n : ℕ}
    (f : EquivariantHom A (piRepresentation A n)) : Fin n -> k :=
  fun i => cert.scalarOf (coordinateHom A f i)

theorem coordinate_scalarsToHom
    (A : Representation G k V) {n : ℕ} (a : Fin n -> k) (i : Fin n) :
    coordinateHom A (scalarsToHom A a) i = scalarEndo A (a i) := by
  apply EquivariantHom.ext
  ext x
  rfl

/-- Core max-cut theorem: after same-action finite-copy recognition and a Schur
certificate, the multiplicity Hom carrier is exactly `n` scalar coordinates. -/
def equivariantHomFiniteCopiesEquivScalars
    (A : Representation G k V) (cert : SchurScalarCertificate A) (n : ℕ) :
    EquivariantHom A (piRepresentation A n) ≃ (Fin n -> k) where
  toFun := homToScalars A cert
  invFun := scalarsToHom A
  left_inv := by
    intro f
    apply EquivariantHom.ext
    ext x i
    change cert.scalarOf (coordinateHom A f i) • x = f.toLinearMap x i
    exact (cert.scalar_spec (coordinateHom A f i) x).symm
  right_inv := by
    intro a
    funext i
    rw [homToScalars, coordinate_scalarsToHom]
    exact cert.scalarOf_scalarEndo (a i)

/-- Specialization used once the lawful post-recognition dimension compiler has
already forced the Monster copy count to 90. -/
def ninetyMultiplicityCoordinates
    (A : Representation G k V) (cert : SchurScalarCertificate A) :
    EquivariantHom A (piRepresentation A 90) ≃ (Fin 90 -> k) :=
  equivariantHomFiniteCopiesEquivScalars A cert 90

/-! ## Coordinate evaluation / recovery

Before introducing a tensor product, the finite-copy carrier already has a
literal evaluation/recovery formula.  This is the exact algebraic content needed
for a future `H tensor S -> W` theorem: every finite-copy vector is a sum of
rank-one evaluations against the scalar coordinate basis.
-/

/-- Kronecker scalar basis on the multiplicity coordinate space. -/
def scalarBasis {n : ℕ} (i : Fin n) : Fin n -> k :=
  fun j => if i = j then 1 else 0

/-- Rank-one evaluation of one constituent vector against one multiplicity
coordinate vector. -/
def coordinateEvaluation {n : ℕ} (x : V) (a : Fin n -> k) : Fin n -> V :=
  fun j => a j • x

/-- Every vector in `H^n` is recovered exactly as the sum of its coordinate
rank-one evaluations.  No Monster-specific source input is used. -/
theorem coordinateEvaluation_recovery {n : ℕ} (w : Fin n -> V) :
    (fun j => ∑ i : Fin n, coordinateEvaluation (w i) (scalarBasis i) j) = w := by
  funext j
  simp [coordinateEvaluation, scalarBasis]

/-- After the Schur identification, an equivariant Hom coordinate vector acts by
the same rank-one evaluation formula on the diagonal finite-copy model. -/
theorem schurCoordinateEvaluation_agrees
    (A : Representation G k V) (cert : SchurScalarCertificate A) {n : ℕ}
    (f : EquivariantHom A (piRepresentation A n)) (x : V) :
    coordinateEvaluation x (homToScalars A cert f) = f.toLinearMap x := by
  funext i
  change cert.scalarOf (coordinateHom A f i) • x = f.toLinearMap x i
  exact (cert.scalar_spec (coordinateHom A f i) x).symm

inductive BareNinetyCreatesMonsterMultiplicity : Prop
inductive CharacterFamilyCreatesSuzukiAction : Prop

theorem bareNinetyDoesNotCreateMonsterMultiplicity :
    ¬ BareNinetyCreatesMonsterMultiplicity := by intro h; cases h

theorem characterFamilyDoesNotCreateSuzukiAction :
    ¬ CharacterFamilyCreatesSuzukiAction := by intro h; cases h

structure Boundary where
  genericFiniteCopyActionTyped : Bool
  proofRelevantSchurCertificateTyped : Bool
  genericSchurCoordinateCompilerSourceWritten : Bool
  ninetyCoordinateSpecializationSourceWritten : Bool
  coordinateEvaluationRecoverySourceWritten : Bool
  actualMonsterHZetaAttachmentPaidHere : Bool
  actualSuzukiActionPaidHere : Bool
  absoluteZetaOrientationPaidHere : Bool
  tensorEvaluationEquivalencePaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  genericFiniteCopyActionTyped := true
  proofRelevantSchurCertificateTyped := true
  genericSchurCoordinateCompilerSourceWritten := true
  ninetyCoordinateSpecializationSourceWritten := true
  coordinateEvaluationRecoverySourceWritten := true
  actualMonsterHZetaAttachmentPaidHere := false
  actualSuzukiActionPaidHere := false
  absoluteZetaOrientationPaidHere := false
  tensorEvaluationEquivalencePaidHere := false

end

end Synthesis.MonsterMultiplicitySchurCoordinates
