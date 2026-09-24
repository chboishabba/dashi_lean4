/-!
# Lean mirror of `DASHI/Core/ContextIndexedEncoding.agda`

The encoding is explicitly indexed by a context.  Coherence of context
transport is not part of the base record in the Agda source, so it remains an
explicit proposition (`DependentProjectionTheorem`) rather than being inferred
from the interface.  The canonical unit-valued instance proves that proposition
constructively.  Its promotion gate is definitionally `false`.
-/

namespace AgdaMirror.ContextIndexedEncoding

/-- A context-indexed projection together with transport, residual, and guard
metadata. -/
structure ContextIndexedEncoding (Carrier Context Observable : Type) where
  π : Carrier → Context → Observable
  transport : Context → Context → Observable → Observable
  residual : Context → Context → Carrier → Type
  contextDependent : Bool
  contextDependentIsTrue : contextDependent = true
  promotionGateCarrier : Type
  promotionGateClosed : promotionGateCarrier → Bool
  encodingGuards : List String
  forbiddenPromotions : List String
  allowedOperations : List String
  encodingReading : String

/-- The DASHI-safe canonical instance.  In particular, every promotion flag is
`false`; no promotion authority is introduced. -/
def canonicalContextIndexedEncoding : ContextIndexedEncoding Unit Unit Unit where
  π := fun _ _ => ()
  transport := fun _ _ o => o
  residual := fun _ _ _ => Unit
  contextDependent := true
  contextDependentIsTrue := rfl
  promotionGateCarrier := Unit
  promotionGateClosed := fun _ => false
  encodingGuards :=
    ["noContextIndependentPromotion", "noCrossContextShortcut",
      "authorityRequiresContextClosure"]
  forbiddenPromotions :=
    ["contextFreeProjection", "carrierPromotedWithoutContext",
      "observableDetachedFromContext"]
  allowedOperations :=
    ["contextDependentProjection", "contextTransport", "residualMeasurement",
      "contextScopedCalibration"]
  encodingReading :=
    "Context-indexed encoding: π : Carrier × Context → Observable.  No context-independent promotion allowed without context closure gate."

/-- The four coherence and non-promotion obligations called the dependent
projection theorem by the Agda source.  For a general encoding these are
additional obligations, not consequences of the record fields. -/
def DependentProjectionTheorem {H Γ O : Type}
    (enc : ContextIndexedEncoding H Γ O) : Prop :=
  enc.contextDependent = true ∧
  (∀ x γ γ', enc.π x γ' = enc.transport γ γ' (enc.π x γ)) ∧
  (∀ γ o, enc.transport γ γ o = o) ∧
  (∀ pg : enc.promotionGateCarrier, enc.promotionGateClosed pg = true → False)

/-- The canonical unit-valued encoding satisfies all four obligations. -/
theorem dependentProjectionTheoremCanonical :
    DependentProjectionTheorem canonicalContextIndexedEncoding := by
  exact ⟨rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ h => Bool.noConfusion h⟩

/-- Non-promotion receipt for a context-indexed encoding. -/
structure ContextIndexedEncodingNonPromotionCertificate
    {Carrier Context Observable : Type}
    (enc : ContextIndexedEncoding Carrier Context Observable) where
  contextDependent : Bool
  contextDependentIsTrue : contextDependent = true
  noCrossContextPromotion : Bool
  noCrossContextPromotionIsTrue : noCrossContextPromotion = true
  guardsMatch : enc.encodingGuards =
    ["noContextIndependentPromotion", "noCrossContextShortcut",
      "authorityRequiresContextClosure"]
  certificateReading : String

/-- Canonical non-promotion receipt.  The `true` certificate fields assert
context dependence and blocking of cross-context promotion; the actual
promotion gate itself remains `false`. -/
def canonicalContextIndexedEncodingNonPromotionCertificate :
    ContextIndexedEncodingNonPromotionCertificate
      canonicalContextIndexedEncoding where
  contextDependent := true
  contextDependentIsTrue := rfl
  noCrossContextPromotion := true
  noCrossContextPromotionIsTrue := rfl
  guardsMatch := rfl
  certificateReading :=
    "The canonical context-indexed encoding is non-promoting: all abstract carriers are Unit, context dependence is asserted, and the promotion gate blocks cross-context shortcuts."

/-- Explicit check of the authority boundary on the canonical promotion gate. -/
theorem canonicalPromotionGateClosed_false (pg : Unit) :
    canonicalContextIndexedEncoding.promotionGateClosed pg = false := rfl

end AgdaMirror.ContextIndexedEncoding
