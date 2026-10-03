import Integration.C2TateIntertwinerTransport

/-!
# C2 Tate transport from an actual group conjugacy

The generic Tate transport owner asks for an additive equivalence `φ` satisfying

  φ (g₀ x) = g₁ (φ x).

For the Monster-local 2B programme the source datum is naturally stronger:
a group representation together with an element `r` carrying one selected 2B
involution to another.  At group level it is enough to have

  r * a = b * r.

This file compiles that group-level relation automatically into the exact
intertwiner consumed by `C2TateIntertwinerTransport`.

No Monster representation is invented here.  The remaining source obligation
is precisely an actual additive representation of the relevant local group on
the integral Moonshine carrier, together with the sourced group relation.
-/

namespace Integration.C2TateTransportFromGroupConjugacy

namespace T := Integration.C2TateIntertwinerTransport

variable {G M : Type*} [Group G] [AddCommGroup M]

/-- Additive action underlying one group element. -/
def actionAddHom (ρ : G →* (M ≃+ M)) (g : G) : M →+ M :=
  (ρ g).toAddMonoidHom

/-- Additive equivalence underlying one transport element. -/
def actionAddEquiv (ρ : G →* (M ≃+ M)) (g : G) : M ≃+ M :=
  ρ g

/-- A group-level commutation/conjugacy relation compiles to the exact
additive intertwiner required by Tate transport. -/
theorem intertwines_of_group_relation
    (ρ : G →* (M ≃+ M))
    {a b r : G}
    (hrel : r * a = b * r) :
    ∀ x : M,
      actionAddEquiv ρ r (actionAddHom ρ a x)
        =
      actionAddHom ρ b (actionAddEquiv ρ r x) := by
  intro x
  have hρ : ρ (r * a) = ρ (b * r) := congrArg ρ hrel
  have hx := congrArg (fun e : M ≃+ M => e x) hρ
  simpa [actionAddHom, actionAddEquiv] using hx

/-- The same group relation transports ordinary Tate-H⁰ representative
conditions exactly. -/
theorem hhat0_transport_of_group_relation
    (ρ : G →* (M ≃+ M))
    {a b r : G}
    (hrel : r * a = b * r)
    (x : M) :
    (T.Fixed (actionAddHom ρ a) x ∧
      ¬ T.NormImage (actionAddHom ρ a) x)
      ↔
    (T.Fixed (actionAddHom ρ b) (actionAddEquiv ρ r x) ∧
      ¬ T.NormImage (actionAddHom ρ b) (actionAddEquiv ρ r x)) :=
  T.hhat0_representative_transport
    (actionAddHom ρ a)
    (actionAddHom ρ b)
    (actionAddEquiv ρ r)
    (intertwines_of_group_relation ρ hrel)
    x

/-- Likewise for ordinary Tate-H¹ representative conditions. -/
theorem hhat1_transport_of_group_relation
    (ρ : G →* (M ≃+ M))
    {a b r : G}
    (hrel : r * a = b * r)
    (x : M) :
    (T.NormKernel (actionAddHom ρ a) x ∧
      ¬ T.DiffImage (actionAddHom ρ a) x)
      ↔
    (T.NormKernel (actionAddHom ρ b) (actionAddEquiv ρ r x) ∧
      ¬ T.DiffImage (actionAddHom ρ b) (actionAddEquiv ρ r x)) :=
  T.hhat1_representative_transport
    (actionAddHom ρ a)
    (actionAddHom ρ b)
    (actionAddEquiv ρ r)
    (intertwines_of_group_relation ρ hrel)
    x

/-- Concrete source socket for one local conjugacy transport.  In the 2B-pure
Klein-four application `a` and `b` are two nonidentity 2B elements and `r` is
the sourced local order-three transporter. -/
structure GroupConjugacyTateReceipt (ρ : G →* (M ≃+ M)) where
  sourceInvolution : G
  targetInvolution : G
  transporter : G
  groupRelation :
    transporter * sourceInvolution = targetInvolution * transporter

namespace GroupConjugacyTateReceipt

variable (ρ : G →* (M ≃+ M))

/-- Every group-level receipt produces the exact additive intertwiner needed
by the existing Tate algebra. -/
theorem intertwines (R : GroupConjugacyTateReceipt ρ) :
    ∀ x : M,
      actionAddEquiv ρ R.transporter
          (actionAddHom ρ R.sourceInvolution x)
        =
      actionAddHom ρ R.targetInvolution
          (actionAddEquiv ρ R.transporter x) :=
  intertwines_of_group_relation ρ R.groupRelation

end GroupConjugacyTateReceipt

end Integration.C2TateTransportFromGroupConjugacy
