import Integration.Registry
import Integration.RiemannReflection
import Integration.RiemannStrip
import Integration.RiemannSubstrate
import Integration.RiemannXiSymmetry
import Spine.RiemannBridge

/-!
# The RH/zeta analytic lane as one domain of the global TOE registry

`Integration.Registry` closes with the remark that it contains *no analytic
row*: every carrier there is finite and every distance a natural number.  This
module adds the analytic lane as a domain, in the same machine-checked
vocabulary, so that the four-level classification covers it too:

* `analyticEntries` — the positive rows, each carrying its evidence
  constructor, hence its level.  Levels iv here are all preservation or
  transport theorems relating the analytic lane's carriers to the *common
  kernel* — the ternary hub (`Integration.TernaryHub`), the fixed ⊕ transverse
  decomposition (`Spine.RealC2`), the exact `C₃` phase algebra
  (`Spine.TernaryPhase`) and the generic two-regime envelope
  (`Spine.TwoRegime`).
* `analyticBoundaries` — the refuted identifications, each carrying its
  refutation.  These are the rows that stop the lane's vocabulary from being
  read as more than it is: the analytic carriers are *not* the hub's carrier,
  the strip's symmetry group is *not* ternary, and the generic envelope does
  *not* dominate a lattice tail.
* `analyticSockets` — the typed interfaces that constrain nothing: the abstract
  envelope producer, the `ℕ` ledgers, the analytic substrate tower whose
  `RiemannHypothesisFor` predicate takes both truth values across inhabitants,
  and the lane's xi-zero-symmetry and Hilbert–Pólya interfaces.

**Scope.**  No row asserts anything about the Riemann zeta function, its zeros,
or the Riemann hypothesis, and none discharges an analytic hypothesis: the
statements are about `ℂ` as a set with two involutions, about a finite phase
carrier, about a discrete displacement model, and about records.  The analytic
frontier (complex continuation, tails, short-interval prime sums, uniform
tapers) belongs to the specialist lane and is deliberately untouched here; the
remaining obligations are listed in `RH_TOE_DOMAIN_MAP.md`.
-/

namespace Integration.RiemannDomain

open Integration.Levels
open Integration.RiemannReflection
open Integration.RiemannStrip
open Integration.RiemannSubstrate
open Integration.RiemannXiSymmetry
open Complex ComplexConjugate
open AgdaMirror.DASHIAlgebra (Trit)

/-! ## The positive rows -/

/-- The analytic lane's rows of the global registry. -/
noncomputable def analyticEntries : List Entry :=
  [ { source := "RiemannReflectionOrbitDefectExact.CentredReflectionState"
      target := "ternary hub polarity × magnitude"
      evidence := .provedTransport centredPolarTransport
      note := "Level iv: the lane's reflection carrier is the hub's digit \
               together with a magnitude, and the reflection is the hub's \
               polarity involution on the digit coordinate.  The Agda states \
               only an orbit-shape analogy." }
  , { source := "RiemannReflectionOrbitDefectExact.reflect"
      target := "Trit.inv (ternary hub polarity)"
      evidence := .provedEquivariance sideTrit reflect Trit.inv sideTrit_reflect
      note := "Level iv as a preservation theorem: surjective, not injective \
               (`sideTrit_not_injective`); the magnitude is forgotten." }
  , { source := "RiemannReflectionC3OrbitShapeBridgeExact.C3Phase"
      target := "ternary hub carrier (Trit) with polarity"
      evidence := .provedTransport c3Transport
      note := "Level iv: the lane's three-phase carrier with `invertC3Phase` \
               is the hub carrier with `Trit.inv`." }
  , { source := "RiemannReflectionC3OrbitShapeBridgeExact.phaseValue"
      target := "the cube roots of unity of Spine.TernaryPhase"
      evidence := .provedEquivariance phaseC invertC3Phase (fun z : ℂ => conj z) phaseC_invert
      note := "Level iv: phase inversion is complex conjugation, and the orbit \
               sum vanishes in ℂ (`phaseC_sum`), where the Agda proves the \
               cancellation only inside its own finite cyclotomic model." }
  , { source := "MonsterC3CyclotomicEvaluationExact.Cyclotomic3 (the lane's only \
                 cross-domain Agda import)"
      target := "the subring ℤ[ζ] ⊆ ℂ of Spine.TernaryPhase"
      evidence := .provedPreservation evalC3 (fun p q => evalC3 (addC3 p q))
        (fun z w : ℂ => z + w) (fun p q => (evalC3_add p q).symm)
      note := "Level iv: the Agda's integer-pair model of `a + bζ` evaluates \
               additively and injectively (`evalC3_injective`) into `ℂ`, and \
               its computational orbit cancellation is the vanishing of \
               `1 + ζ + ζ²` there (`evalC3_orbit_cancels`)."
    }
  , { source := "critical-strip reflection s ↦ 1 - conj s"
      target := "the C₂ generator of Spine.RealC2 (fixed ⊕ transverse)"
      evidence := .provedEquivariance stripC2 critReflect (fun v => Spine.RealC2.swap v)
        (fun s => (stripC2_swap s).symm)
      note := "Level iv: the functional-equation-plus-conjugation involution is \
               the kernel's binary contrast generator; the critical line is its \
               fixed locus (`critReflect_fixed_iff`, `stripC2_fixed_iff`) and \
               the displacement is the transverse coordinate." }
  , { source := "RiemannXiSymmetryExact rational symmetry plane"
      target := "the same three involutions on ℂ"
      evidence := .provedEquivariance qToC criticalReflection critReflect qToC_critical
      note := "Level iv: the source's exact ℚ coordinate plane evaluates \
               injectively into ℂ (`qToC_injective`), carrying its conjugation, \
               functional-equation reflection and critical reflection to the \
               corresponding maps of `Integration.RiemannStrip` \
               (`qToC_conjugate`, `qToC_functional`, `qToC_critical`) and its \
               critical line onto `Re s = 1/2` (`qToC_criticalLine_iff`)."
    }
  , { source := "critical-strip displacement Re s − 1/2"
      target := "the signed transverse coordinate of the kernel"
      evidence := .provedEquivariance displacement critReflect (fun x : ℝ => -x)
        displacement_critReflect
      note := "Level iv: the reflection negates the displacement, which vanishes \
               exactly on the critical line." }
  , { source := "critical-strip polarity classifier"
      target := "ternary hub carrier (Trit)"
      evidence := .provedEquivariance stripTrit critReflect Trit.inv stripTrit_critReflect
      note := "Level iv as a preservation theorem only: surjective but not \
               injective (`stripTrit_not_injective`), and the boundary rows \
               record that the analytic carrier is not the hub carrier." }
  , { source := "RiemannReflectionOrbitDefectExact discrete model"
      target := "the real displacement line"
      evidence := .provedEquivariance modelDisplacement reflect (fun x : ℝ => -x)
        modelDisplacement_reflect
      note := "Level iv: the Agda's ℕ-magnitude model embeds in ℝ \
               (`modelDisplacement_injective`) compatibly with reflection, \
               magnitude, squared defect and polarity.  This is the *available* \
               half of the adapter obligation; that actual zero data lands in \
               the model is not proved anywhere." }
  , { source := "Spine.TwoRegime.envelope (kernel frequency estimate)"
      target := "the reflection-invariant magnitude"
      evidence := .provedEquivariance (Spine.TwoRegime.envelope 1 1) (fun x : ℝ => -x)
        (fun y : ℝ => y) (fun x => envelope_neg 1 1 x)
      note := "Level iv: the generic envelope is even, so it is a function of \
               the displacement magnitude alone; stated in the row at K₀=K₁=1, \
               `envelope_neg` is general." }
  , { source := "RiemannPhiCoshCoercivityReductionExact.PhiCoshCoercivityLedger"
      target := "a natural-number margin"
      evidence := .recordDependency (fun l : Spine.RiemannBridge.CoshCoercivityLedger => l.excess)
      note := "Level ii and no higher: the ledger is a stored ℕ inequality \
               (`nat_margin_iff_le`) and is inhabited with all fields zero, so \
               it carries no analytic content by itself." }
  , { source := "RiemannAnalyticSubstrate.RiemannHypothesisFor"
      target := "the Riemann hypothesis"
      evidence := .vocabulary "zeta"
      note := "Level i and no higher.  The tower's fields are abstract types; \
               both truth values of the predicate occur among its inhabitants \
               (`substrate_does_not_constrain_rh`), so the tower is a socket, \
               not a subject.  No zeta function is defined anywhere in this \
               corpus." }
  ]

/-- The level of every analytic row, in order — read off the evidence
constructors, not asserted. -/
theorem analyticEntries_levels :
    analyticEntries.map Entry.level =
      [.provedTransport, .provedTransport, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport, .provedTransport,
       .provedTransport, .provedTransport, .provedTransport, .recordDependency,
       .vocabulary] := rfl

/-! ## The negative rows -/

/-- Refuted identifications in the analytic lane, each with its refutation. -/
def analyticBoundaries : List Boundary :=
  [ { source := "RiemannReflectionC3OrbitShapeBridgeExact.C3Phase"
      target := "the lane's reflection carrier"
      statement := "The Agda `Bool` flag `c3AndZetaCarriersIdentified = false`, \
                    as a theorem: the reflection carrier is infinite."
      claim := Nonempty (C3Phase ≃ CentredState)
      refutation := c3_not_equiv_centred }
  , { source := "the lane's reflection carrier"
      target := "the ternary hub carrier"
      statement := "Only the sign transports; the magnitude coordinate survives."
      claim := Nonempty (CentredState ≃ Trit)
      refutation := centred_not_equiv_trit }
  , { source := "orbit-role layer of the C₃/zeta comparison"
      target := "a bijection of the nontrivial roles"
      statement := "The zeta side's inverse-pair role is infinite, the C₃ side's \
                    has two elements: the analogy stops at the role layer."
      claim := Nonempty ({x : CentredState // centredOrbitRole x = .inversePairRole} ≃
        {x : C3Phase // c3OrbitRole x = .inversePairRole})
      refutation := role_fibres_not_equiv }
  , { source := "critical-strip polarity classifier"
      target := "an identification of the strip with the hub carrier"
      statement := "The sign of the displacement forgets the displacement."
      claim := Function.Injective stripTrit
      refutation := stripTrit_not_injective }
  , { source := "the strip's symmetry group (functional equation, conjugation)"
      target := "the ternary hub carrier"
      statement := "The group is Klein four — four elements, all involutions — \
                    so the analytic symmetry is binary, not ternary."
      claim := Nonempty (StripSymmetry ≃ Trit)
      refutation := stripSymmetry_not_equiv_trit }
  , { source := "Spine.TwoRegime.envelope on an arithmetic grid"
      target := "the lane's lattice-tail domination"
      statement := "The envelope's own bound along a grid is harmonic, hence \
                    not summable: a further analytic input is required."
      claim := Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) * 1))
      refutation := Spine.RiemannBridge.grid_envelope_not_summable one_pos one_pos }
  ]

/-! ## The sockets -/

/-- Typed interfaces of the analytic lane that constrain nothing, each with a
proof of the underdetermination. -/
def analyticSockets : List Socket :=
  [ { site := "RiemannAnalyticSubstrate.AnalyticSubstrate"
      role := "owning a complex-analytic zeta function and its critical line"
      underdetermined :=
        (∃ A : AnalyticSubstrate, Nonempty (RiemannHypothesisFor A)) ∧
        (∃ A : AnalyticSubstrate, ¬ Nonempty (RiemannHypothesisFor A))
      witness := substrate_does_not_constrain_rh }
  , { site := "RiemannMixedKernelEnvelopeExact.ComplexPhiKernelEnvelopeProducer"
      role := "supplying the pairwise and aggregate kernel envelope bounds"
      underdetermined := ∀ e : ℕ → ℕ,
        ∃ p : Spine.RiemannBridge.AbstractEnvelopeProducer,
          p.PairIndex = ℕ ∧ HEq p.envelope e
      witness := fun e => Spine.RiemannBridge.producer_socket_is_contentless ℕ e }
  , { site := "RiemannXiSymmetryExact.XiZeroSymmetry"
      role := "owning the zero set of ξ and its closure under the two symmetries"
      underdetermined :=
        (∃ S : XiZeroSymmetry, ∀ p, Nonempty (S.isXiZero p)) ∧
        (∃ S : XiZeroSymmetry, ∀ p, ¬ Nonempty (S.isXiZero p))
      witness := xiZeroSymmetry_is_socket }
  , { site := "RiemannXiSymmetryExact.HilbertPolyaCandidate"
      role := "owning a self-adjoint operator whose spectrum gives the zeros"
      underdetermined := ∀ f : ℕ → ℚ,
        ∃ C : HilbertPolyaCandidate, C.Eigenvector = ℕ ∧ HEq C.eigenvalue f
      witness := hilbertPolya_is_socket }
  , { site := "the lane's ℕ ledgers (cosh coercivity, centred grid, mixed envelope)"
      role := "recording that an analytic quantity stays inside a budget"
      underdetermined :=
        (∃ l : Spine.RiemannBridge.CoshCoercivityLedger, l.alphaSq = 0 ∧ l.excess = 0) ∧
        (∃ g : Spine.RiemannBridge.CenteredGridLedger, g.fullEnergy = 0 ∧ g.finiteEnergy = 0) ∧
        (∃ e : Spine.RiemannBridge.MixedKernelEnvelopeLedger 0 0, e.kernelEnvelope = 0)
      witness := Spine.RiemannBridge.ledgers_have_trivial_inhabitants }
  ]

/-! ## The domain, as one checked bundle -/

/-- Everything the analytic domain contributes to the global map, as a single
record of statements: the kernel bridges that are proved, the identifications
that are refuted, and the interfaces that are empty. -/
structure AnalyticDomainSummary where
  /-- The critical line is exactly the fixed locus of the lane's involution. -/
  critical_line_is_fixed_locus : ∀ s : ℂ, critReflect s = s ↔ s.re = 1 / 2
  /-- The involution is the kernel's binary contrast generator. -/
  reflection_is_C2 : ∀ s : ℂ, Spine.RealC2.swap (stripC2 s) = stripC2 (critReflect s)
  /-- The displacement is the transverse coordinate and is negated. -/
  displacement_is_transverse : ∀ s : ℂ,
    (stripC2 s - stripCentre) ∈ Spine.RealC2.transverse ∧
      displacement (critReflect s) = - displacement s
  /-- The lane's polarity classifiers are the ternary hub's polarity. -/
  polarity_is_hub : (∀ s : ℂ, stripTrit (critReflect s) = Trit.inv (stripTrit s)) ∧
    (∀ x : CentredState, sideTrit (reflect x) = Trit.inv (sideTrit x))
  /-- The discrete reflection model embeds in the real displacement line. -/
  model_embeds : Function.Injective modelDisplacement ∧
    (∀ x : CentredState, modelDisplacement x ^ 2 = (squaredDefect x : ℝ))
  /-- The three-phase carrier is the hub carrier, realised by actual cube roots
  of unity whose orbit sum vanishes. -/
  phases_are_cube_roots : (∀ x : C3Phase, phaseC x ^ 3 = 1) ∧
    phaseC .identityPhase + phaseC .zetaPhase + phaseC .zetaInversePhase = 0
  /-- The Moonshine cyclotomic carrier imported by the lane evaluates faithfully
  into `ℂ`. -/
  cyclotomic_evaluates : Function.Injective evalC3 ∧
    (∀ p q, evalC3 (addC3 p q) = evalC3 p + evalC3 q)
  /-- The source's rational symmetry plane evaluates faithfully into `ℂ`. -/
  rational_plane_evaluates : Function.Injective qToC ∧
    (∀ p, qToC (criticalReflection p) = critReflect (qToC p)) ∧
    (∀ p, CriticalLine p ↔ (qToC p).re = 1 / 2)
  /-- Negative: the analytic carriers are not the hub carrier. -/
  carriers_not_identified : ¬ Nonempty (CentredState ≃ Trit) ∧
    ¬ Nonempty (C3Phase ≃ CentredState) ∧ ¬ Function.Injective stripTrit
  /-- Negative: the strip's symmetry group is Klein four, not ternary. -/
  symmetry_is_binary : (∀ g : StripSymmetry, ∀ s : ℂ, act g (act g s) = s) ∧
    ¬ Nonempty (StripSymmetry ≃ Trit)
  /-- Socket: the analytic substrate tower does not constrain its own RH
  predicate. -/
  substrate_is_socket :
    (∃ A : AnalyticSubstrate, Nonempty (RiemannHypothesisFor A)) ∧
    (∃ A : AnalyticSubstrate, ¬ Nonempty (RiemannHypothesisFor A))
  /-- Socket: the lane's ℕ ledgers are inhabited trivially. -/
  ledgers_are_sockets :
    ∃ l : Spine.RiemannBridge.CoshCoercivityLedger, l.alphaSq = 0 ∧ l.excess = 0

/-- The analytic domain summary, inhabited. -/
theorem analyticDomain : AnalyticDomainSummary where
  critical_line_is_fixed_locus := critReflect_fixed_iff
  reflection_is_C2 := stripC2_swap
  displacement_is_transverse := fun s =>
    ⟨stripC2_sub_centre_mem_transverse s, displacement_critReflect s⟩
  polarity_is_hub := ⟨stripTrit_critReflect, sideTrit_reflect⟩
  model_embeds := ⟨modelDisplacement_injective, modelDisplacement_sq⟩
  phases_are_cube_roots := ⟨phaseC_cube, phaseC_sum⟩
  cyclotomic_evaluates := ⟨evalC3_injective, evalC3_add⟩
  rational_plane_evaluates := ⟨qToC_injective, qToC_critical, qToC_criticalLine_iff⟩
  carriers_not_identified :=
    ⟨centred_not_equiv_trit, c3_not_equiv_centred, stripTrit_not_injective⟩
  symmetry_is_binary := ⟨act_involutive, stripSymmetry_not_equiv_trit⟩
  substrate_is_socket := substrate_does_not_constrain_rh
  ledgers_are_sockets := Spine.RiemannBridge.ledgers_have_trivial_inhabitants.1

end Integration.RiemannDomain
