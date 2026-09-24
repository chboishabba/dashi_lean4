import Integration.StructureMorphism

/-!
# Base, fibre, transport, measurement

The architecture this file owns is: a base space, a total space of states over
it, transport of fibre states along a move in the base, and a measurement that
observes the total space.  The question is then whether the measurement square

```
        E_p --T--> E_q
         |          |
        obs        obs
         v          v
        F_p --T̄--> F_q
```

commutes exactly, approximately, or not at all — which is again the tiering of
`Integration.StructureMorphism`, now applied to a bundle.

Contents.

* `Bundle`, `Transport`, `BundleObserver` — the data;
* `MeasuredExactly` — the measurement square, defined as the exact square of the
  owner rather than as a new notion;
* `measured_of_factors` — an observer that factors through a transport-invariant
  quantity measures it exactly;
* `not_measured_of_collision` — and the failure case: a measurement that
  identifies two fibre states whose transports differ cannot have any effective
  transport downstream;
* `pullbackDist`, `pullbackDist_self_of_collision` — **the metric statement**: a
  measurement induces a pseudodistance on the total space, and if the
  measurement is not injective then two distinct states are at measured distance
  zero.  This is the precise form of "coarse distance zero does not imply fine
  distance zero"; `pullbackDist_le_of_nonexpansive` records the one implication
  that does hold.

The base is an arbitrary type; no manifold, metric tensor or spacetime structure
is constructed, and no claim is made that any particular system is described by
this bundle.
-/

namespace Integration.ObserverBundle

open Integration.StructureMorphism

/-! ## The data -/

/-- A bundle: a total space with a projection to the base. -/
structure Bundle (M : Type*) where
  /-- The total space of states. -/
  Total : Type*
  /-- The projection to the base. -/
  proj : Total → M

/-- Transport of total-space states along a move in the base. -/
structure Transport {M : Type*} (E : Bundle M) where
  /-- Move a state from the fibre over `p` to the fibre over `q`. -/
  move : M → M → E.Total → E.Total
  /-- Transport lands in the intended fibre. -/
  move_proj : ∀ p q e, E.proj (move p q e) = q

/-- A measurement of the total space. -/
structure BundleObserver {M : Type*} (E : Bundle M) (Obs : Type*) where
  /-- The measured value of a state. -/
  obs : E.Total → Obs

variable {M Obs : Type*} {E : Bundle M}

/-- The measurement square commutes exactly for the move `p → q`, with the
stated downstream transport. -/
def MeasuredExactly (T : Transport E) (O : BundleObserver E Obs) (p q : M)
    (Tbar : Obs → Obs) : Prop :=
  Exact O.obs (T.move p q) Tbar

/-- A measurement that factors through a transport-invariant quantity measures
the transport exactly, with the identity downstream. -/
theorem measured_of_factors {T : Transport E} {O : BundleObserver E Obs} {p q : M}
    (hinv : ∀ e, O.obs (T.move p q e) = O.obs e) : MeasuredExactly T O p q id :=
  fun e => hinv e

/-- **The failure case.**  If the measurement identifies two states whose
transports it distinguishes, then *no* downstream transport closes the square. -/
theorem not_measured_of_collision {T : Transport E} {O : BundleObserver E Obs} {p q : M}
    {e₁ e₂ : E.Total} (hcoll : O.obs e₁ = O.obs e₂)
    (hsplit : O.obs (T.move p q e₁) ≠ O.obs (T.move p q e₂)) :
    ∀ Tbar : Obs → Obs, ¬ MeasuredExactly T O p q Tbar := by
  intro Tbar h
  apply hsplit
  rw [h e₁, h e₂, hcoll]

/-! ## Distances: measured versus fine -/

variable [PseudoMetricSpace Obs]

/-- The pseudodistance a measurement induces on the total space. -/
def pullbackDist (O : BundleObserver E Obs) (e₁ e₂ : E.Total) : ℝ :=
  dist (O.obs e₁) (O.obs e₂)

theorem pullbackDist_comm (O : BundleObserver E Obs) (e₁ e₂ : E.Total) :
    pullbackDist O e₁ e₂ = pullbackDist O e₂ e₁ := dist_comm _ _

theorem pullbackDist_triangle (O : BundleObserver E Obs) (e₁ e₂ e₃ : E.Total) :
    pullbackDist O e₁ e₃ ≤ pullbackDist O e₁ e₂ + pullbackDist O e₂ e₃ :=
  dist_triangle _ _ _

/-- **Measured distance zero does not imply equality.**  A non-injective
measurement puts two distinct states at measured distance zero. -/
theorem pullbackDist_self_of_collision (O : BundleObserver E Obs) {e₁ e₂ : E.Total}
    (hcoll : O.obs e₁ = O.obs e₂) : pullbackDist O e₁ e₂ = 0 := by
  simp [pullbackDist, hcoll]

/-- The implication that does hold: if the measurement is nonexpansive for a
finer distance, the measured distance is bounded by the fine one — never the
other way round. -/
theorem pullbackDist_le_of_nonexpansive [PseudoMetricSpace E.Total]
    (O : BundleObserver E Obs) (hne : ∀ a b : E.Total, dist (O.obs a) (O.obs b) ≤ dist a b)
    (e₁ e₂ : E.Total) : pullbackDist O e₁ e₂ ≤ dist e₁ e₂ := hne e₁ e₂

/-- The two statements together, on an explicit bundle: a two-state fibre over a
one-point base, measured by a constant.  The measured distance is identically
zero while the states are distinct. -/
theorem coarse_zero_fine_distinct :
    ∃ (E : Bundle.{0, 0} Unit) (O : BundleObserver E ℝ) (e₁ e₂ : E.Total),
      e₁ ≠ e₂ ∧ pullbackDist O e₁ e₂ = 0 := by
  refine ⟨⟨Bool, fun _ => ()⟩, ⟨fun _ => 0⟩, false, true, ?_, ?_⟩
  · exact Bool.false_ne_true
  · simp [pullbackDist]

end Integration.ObserverBundle
