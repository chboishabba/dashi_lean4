import Mathlib

/-!
# Griess constituent from the fixed conformal line by Maschke

This is a generic representation-theoretic compiler for the weight-two Monster
seam.  It deliberately does not manufacture the actual Monster grade-two
representation or a same-object VOA transport.

Once one has the SAME finite-dimensional characteristic-zero representation
`rho` for the literal grade-two action, together with a nonzero conformal vector
`omega` fixed by the whole group and total finrank `196884`, Maschke supplies an
invariant complement to the conformal line.  Its finrank is forced to be
`196883`.

Thus no independent 196883-dimensional matrix representation is required after
the grade-two FDRep attachment is paid.  The remaining Monster-specific input is
the same-object linear transport of the literal VOA grade-two action and its
conformal vector into this representation-theory surface.
-/

namespace Synthesis.MonsterGriessMaschkeComplement

noncomputable section

universe u

variable {k G V : Type u}
variable [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The line spanned by one group-fixed vector is a subrepresentation. -/
def fixedConformalLine
    (rho : Representation k G V)
    (omega : V)
    (hfixed : ∀ g : G, rho g omega = omega) :
    Subrepresentation rho where
  toSubmodule := k ∙ omega
  apply_mem_toSubmodule := by
    intro g v hv
    rcases Submodule.mem_span_singleton.mp hv with ⟨c, rfl⟩
    simpa [hfixed g] using
      ((k ∙ omega).smul_mem c (Submodule.mem_span_singleton_self omega))

/-- A complement in the subrepresentation lattice induces a complement of the
underlying scalar submodules. -/
theorem isCompl_toSubmodule
    (rho : Representation k G V)
    {A B : Subrepresentation rho}
    (h : IsCompl A B) :
    IsCompl A.toSubmodule B.toSubmodule := by
  apply IsCompl.of_eq
  · simpa using congrArg
      (fun S : Subrepresentation rho => S.toSubmodule)
      h.inf_eq_bot
  · simpa using congrArg
      (fun S : Subrepresentation rho => S.toSubmodule)
      h.sup_eq_top

/-- Maschke supplies an invariant complement to a fixed conformal line, and the
usual dimension formula forces that complement to have finrank 196883 when the
ambient grade-two representation has finrank 196884. -/
theorem existsGriessComplement
    (rho : Representation k G V)
    (omega : V)
    (homega : omega ≠ 0)
    (hfixed : ∀ g : G, rho g omega = omega)
    (hdim : Module.finrank k V = 196884) :
    ∃ C : Subrepresentation rho,
      IsCompl (fixedConformalLine rho omega hfixed) C ∧
      Module.finrank k C.toSubmodule = 196883 := by
  letI : rho.IsSemisimpleRepresentation := by infer_instance
  obtain ⟨C, hC⟩ := exists_isCompl (fixedConformalLine rho omega hfixed)
  refine ⟨C, hC, ?_⟩
  have hline :
      Module.finrank k
        (fixedConformalLine rho omega hfixed).toSubmodule = 1 := by
    change Module.finrank k (k ∙ omega) = 1
    exact finrank_span_singleton homega
  have hsub :
      IsCompl
        (fixedConformalLine rho omega hfixed).toSubmodule
        C.toSubmodule :=
    isCompl_toSubmodule rho hC
  have hsum := Submodule.finrank_add_eq_of_isCompl hsub
  rw [hline, hdim] at hsum
  omega

/-- After Maschke has selected the complement, its own restricted representation
and the inclusion into the ambient grade-two representation are canonical. -/
structure GriessComplementData
    (rho : Representation k G V)
    (omega : V)
    (hfixed : ∀ g : G, rho g omega = omega) where
  constituent : Subrepresentation rho
  complementary : IsCompl (fixedConformalLine rho omega hfixed) constituent
  constituentFinrank : Module.finrank k constituent.toSubmodule = 196883

/-- Package the existential complement into the proof-bearing data consumed by
same-object representation adapters. -/
def chooseGriessComplement
    (rho : Representation k G V)
    (omega : V)
    (homega : omega ≠ 0)
    (hfixed : ∀ g : G, rho g omega = omega)
    (hdim : Module.finrank k V = 196884) :
    GriessComplementData rho omega hfixed := by
  classical
  let C := Classical.choose (existsGriessComplement rho omega homega hfixed hdim)
  have h := Classical.choose_spec (existsGriessComplement rho omega homega hfixed hdim)
  exact
    { constituent := C
      complementary := h.1
      constituentFinrank := h.2 }

/-- The selected constituent automatically carries the restricted group action. -/
def griessRepresentation
    (rho : Representation k G V)
    (omega : V)
    (hfixed : ∀ g : G, rho g omega = omega)
    (data : GriessComplementData rho omega hfixed) :
    Representation k G data.constituent.toSubmodule :=
  data.constituent.toRepresentation

/-- Its inclusion into grade two is literally equivariant. -/
theorem griessInclusion_intertwines
    (rho : Representation k G V)
    (omega : V)
    (hfixed : ∀ g : G, rho g omega = omega)
    (data : GriessComplementData rho omega hfixed)
    (g : G) (x : data.constituent.toSubmodule) :
    rho g x =
      data.constituent.toSubmodule.subtype
        ((griessRepresentation rho omega hfixed data) g x) := by
  rfl

inductive CharacterArithmeticCreatesGradeTwoFDRep : Prop
inductive BasisLabelsCreateVectorCarrier : Prop

theorem characterArithmeticDoesNotCreateGradeTwoFDRep :
    ¬ CharacterArithmeticCreatesGradeTwoFDRep := by
  intro h
  cases h

theorem basisLabelsDoNotCreateVectorCarrier :
    ¬ BasisLabelsCreateVectorCarrier := by
  intro h
  cases h

structure Boundary where
  fixedLineSubrepresentationSourceWritten : Bool
  maschkeComplementSourceWritten : Bool
  complementFinrank196883SourceWritten : Bool
  restrictedGriessRepresentationSourceWritten : Bool
  inclusionIntertwiningSourceWritten : Bool
  actualMonsterGradeTwoFDRepAttachedHere : Bool
  characterArithmeticCreatesGradeTwoFDRep : Bool
  basisLabelsCreateVectorCarrier : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fixedLineSubrepresentationSourceWritten := true
  maschkeComplementSourceWritten := true
  complementFinrank196883SourceWritten := true
  restrictedGriessRepresentationSourceWritten := true
  inclusionIntertwiningSourceWritten := true
  actualMonsterGradeTwoFDRepAttachedHere := false
  characterArithmeticCreatesGradeTwoFDRep := false
  basisLabelsCreateVectorCarrier := false

end

end Synthesis.MonsterGriessMaschkeComplement
