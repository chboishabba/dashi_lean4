import Integration.ThreeCycleTraceSplit
import Integration.ThreeC2TateFibreCycle

/-!
# Three 2B Tate fibres: invariant plus trace-zero splitting

Attribution / provenance:
* visual/conceptual prompt: JMD's supplied GF(27)/GF(4096) Frobenius-orbit diagrams;
* the finite-field identities are standard;
* this file derives a DASHI-specific characteristic-two three-fibre theorem.

The current 2B architecture uses one selected ten-dimensional Tate layer `Q10`
transported around the three nonidentity elements of a 2B-pure Klein four.
After choosing a common transported chart, the external three-fibre carrier is

  Q x Q x Q,

with the C3 generator cyclically permuting the three factors.

This file proves exactly:

  3*dim(Q) = dim(invariants) + dim(trace-zero)

and, when `dim(Q)=10`,

  30 = 10 + 20.

The 20-dimensional trace-zero piece satisfies `tau^2 + tau + 1 = 0`, the
quadratic relation underlying the natural GF(4)-phase reading.  We deliberately
stop short of declaring a same-object scalar-extension equivalence with a
particular finite field until that scalar action is explicitly constructed.
-/

namespace Integration.ThreeC2TateFibreTraceSplit

namespace T := Integration.ThreeCycleTraceSplit

abbrev F2 := T.F2

variable {Q : Type*} [AddCommGroup Q] [Module F2 Q]

/-- Common transported chart for the three selected Tate fibres. -/
abbrev TransportedThreeFibre (Q : Type*) := Q × (Q × Q)

/-- The sourced C3 phase after transporting the three Tate fibres to one common
chart: `(x0,x1,x2) -> (x2,x0,x1)`. -/
def fibreCycle : TransportedThreeFibre Q →ₗ[F2] TransportedThreeFibre Q where
  toFun x := (x.2.2, (x.1, x.2.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical order-three datum on the transported three-fibre carrier. -/
def fibreCycleData : T.ThreeCycleData (V := TransportedThreeFibre Q) where
  tau := fibreCycle
  orderThree := by
    intro x
    rcases x with ⟨x0, x1, x2⟩
    rfl

/-- Coordinate sum in the common transported chart. -/
def fibreSum : TransportedThreeFibre Q →ₗ[F2] Q where
  toFun x := x.1 + x.2.1 + x.2.2
  map_add' _ _ := by module
  map_smul' _ _ := by module

/-- Diagonal embedding of the descended/invariant copy of `Q`. -/
def diagonal : Q →ₗ[F2] TransportedThreeFibre Q where
  toFun x := (x, (x, x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- In the canonical chart the orbit sum is literally diagonalized coordinate
sum. -/
theorem threeTrace_eq_diagonal_sum (x : TransportedThreeFibre Q) :
    T.threeTrace (fibreCycleData (Q := Q)) x = diagonal (fibreSum x) := by
  rcases x with ⟨x0, x1, x2⟩
  ext <;> dsimp [T.threeTrace, fibreCycleData, fibreCycle, diagonal, fibreSum]
  <;> module

/-- The invariant image is exactly the diagonal copy of `Q`. -/
theorem diagonal_mem_trace_range (q : Q) :
    diagonal q ∈ LinearMap.range (T.threeTrace (fibreCycleData (Q := Q))) := by
  apply T.fixed_mem_range_threeTrace (D := fibreCycleData (Q := Q))
  rfl

/-- Linear map from `Q` onto the invariant/range submodule. -/
def diagonalToRange :
    Q →ₗ[F2] LinearMap.range (T.threeTrace (fibreCycleData (Q := Q))) :=
  diagonal.codRestrict _ diagonal_mem_trace_range

theorem diagonalToRange_injective :
    Function.Injective (diagonalToRange (Q := Q)) := by
  intro a b h
  have h' := congrArg (fun y => y.1.1) h
  simpa [diagonalToRange, diagonal] using h'

theorem diagonalToRange_surjective :
    Function.Surjective (diagonalToRange (Q := Q)) := by
  intro y
  have hfix := T.range_threeTrace_is_fixed
    (D := fibreCycleData (Q := Q)) y.2
  rcases y.1 with ⟨x0, x1, x2⟩
  change (x2, (x0, x1)) = (x0, (x1, x2)) at hfix
  have h20 : x2 = x0 := congrArg Prod.fst hfix
  have hrest : (x0, x1) = (x1, x2) := congrArg Prod.snd hfix
  have h01 : x0 = x1 := congrArg Prod.fst hrest
  have h12 : x1 = x2 := congrArg Prod.snd hrest
  refine ⟨x0, ?_⟩
  apply Subtype.ext
  simp only [diagonalToRange, LinearMap.codRestrict_apply, diagonal]
  subst x1
  subst x2
  rfl

/-- Exact recognition of the invariant piece as one copy of `Q`. -/
noncomputable def invariantEquivQ :
    Q ≃ₗ[F2] LinearMap.range (T.threeTrace (fibreCycleData (Q := Q))) :=
  LinearEquiv.ofBijective (diagonalToRange (Q := Q))
    ⟨diagonalToRange_injective, diagonalToRange_surjective⟩

/-- Explicit chart for the trace-zero piece.  In characteristic two,
`(a,b,a+b)` has coordinate sum zero. -/
def traceZeroChart : (Q × Q) →ₗ[F2] TransportedThreeFibre Q where
  toFun p := (p.1, (p.2, p.1 + p.2))
  map_add' _ _ := by ext <;> module
  map_smul' _ _ := by ext <;> module

theorem traceZeroChart_mem_ker (p : Q × Q) :
    traceZeroChart p ∈ LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q))) := by
  change T.threeTrace (fibreCycleData (Q := Q)) (traceZeroChart p) = 0
  rw [threeTrace_eq_diagonal_sum]
  rcases p with ⟨a,b⟩
  ext <;> dsimp [traceZeroChart, fibreSum, diagonal]
  <;> module

/-- Map from two free Q-coordinates onto the trace-zero submodule. -/
def traceZeroToKer :
    (Q × Q) →ₗ[F2] LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q))) :=
  traceZeroChart.codRestrict _ traceZeroChart_mem_ker

theorem traceZeroToKer_injective :
    Function.Injective (traceZeroToKer (Q := Q)) := by
  intro a b h
  have h1 := congrArg (fun y => y.1.1) h
  have h2 := congrArg (fun y => y.1.2.1) h
  apply Prod.ext
  · simpa [traceZeroToKer, traceZeroChart] using h1
  · simpa [traceZeroToKer, traceZeroChart] using h2

theorem traceZeroToKer_surjective :
    Function.Surjective (traceZeroToKer (Q := Q)) := by
  intro y
  rcases y.1 with ⟨x0, x1, x2⟩
  have hy : T.threeTrace (fibreCycleData (Q := Q)) (x0, (x1, x2)) = 0 := by
    simpa using y.2
  rw [threeTrace_eq_diagonal_sum] at hy
  have hs : x0 + x1 + x2 = 0 := by
    have := congrArg Prod.fst hy
    simpa [fibreSum, diagonal] using this
  have hx2 : x2 = x0 + x1 := by
    module at hs ⊢
  refine ⟨(x0,x1), ?_⟩
  apply Subtype.ext
  simp only [traceZeroToKer, LinearMap.codRestrict_apply, traceZeroChart]
  rw [← hx2]

/-- Exact recognition of the trace-zero piece as two copies of `Q`. -/
noncomputable def traceZeroEquivQQ :
    (Q × Q) ≃ₗ[F2] LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q))) :=
  LinearEquiv.ofBijective (traceZeroToKer (Q := Q))
    ⟨traceZeroToKer_injective, traceZeroToKer_surjective⟩

/-- The characteristic-two quadratic phase relation on the actual trace-zero
submodule. -/
theorem traceZero_quadratic_phase
    (x : LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q)))) :
    fibreCycle (fibreCycle x.1) + fibreCycle x.1 + x.1 = 0 :=
  T.quadratic_phase_relation_of_mem_ker
    (D := fibreCycleData (Q := Q)) x.2

/-- The generic direct-sum statement specialized to the transported three Tate
fibres. -/
theorem invariant_traceZero_isCompl :
    IsCompl
      (LinearMap.range (T.threeTrace (fibreCycleData (Q := Q))))
      (LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q)))) :=
  T.threeTrace_range_ker_isCompl (fibreCycleData (Q := Q))

section FiniteDimensional

variable [FiniteDimensional F2 Q]

@[simp]
theorem transportedThreeFibre_finrank :
    Module.finrank F2 (TransportedThreeFibre Q) = 3 * Module.finrank F2 Q := by
  simp [TransportedThreeFibre]
  omega

theorem invariant_finrank :
    Module.finrank F2
      (LinearMap.range (T.threeTrace (fibreCycleData (Q := Q))))
      = Module.finrank F2 Q :=
  (invariantEquivQ (Q := Q)).finrank_eq.symm

theorem traceZero_finrank :
    Module.finrank F2
      (LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q))))
      = 2 * Module.finrank F2 Q := by
  calc
    Module.finrank F2
        (LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q))))
      = Module.finrank F2 (Q × Q) :=
        (traceZeroEquivQQ (Q := Q)).finrank_eq.symm
    _ = 2 * Module.finrank F2 Q := by simp; omega

/-- The promised 30 = 10 + 20 result for a selected Completion10 layer. -/
theorem completionTen_threeFibre_30_eq_10_plus_20
    (hQ : Module.finrank F2 Q = 10) :
    Module.finrank F2 (TransportedThreeFibre Q) = 30
    ∧ Module.finrank F2
        (LinearMap.range (T.threeTrace (fibreCycleData (Q := Q)))) = 10
    ∧ Module.finrank F2
        (LinearMap.ker (T.threeTrace (fibreCycleData (Q := Q)))) = 20 := by
  constructor
  · rw [transportedThreeFibre_finrank, hQ]
  constructor
  · rw [invariant_finrank, hQ]
  · rw [traceZero_finrank, hQ]

end FiniteDimensional

/-- Standard-field name for the quadratic phase target.  The theorem above
constructs the exact `X^2+X+1` operator relation needed for an F4 action, but
this file does not invent an unproved scalar-extension identification. -/
abbrev GF4 := GaloisField 2 2

def gf4ScalarExtensionEquivPaid : Bool := false

def actualQ10ExtractionPaid : Bool := false

def actualMonsterLocalTateIntertwinerPaid : Bool := false

def jmdGF27TraceAnalogyPromotedToSameObject : Bool := false

def jmdNonaryNineAnalogyPromotedTo279Mechanism : Bool := false

end Integration.ThreeC2TateFibreTraceSplit
