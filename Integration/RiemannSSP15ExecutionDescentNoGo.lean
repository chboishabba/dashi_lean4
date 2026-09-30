import Integration.RiemannSSP15RHProducerSameGraphWeld

/-!
# Signed execution cannot reconstruct the selected prime

This is a structural no-go, not an identification with an analytic trace.
An observable can descend to execution effects only when it is constant
on execution fibres. Distinct j-role pointed seeds have identical empty
effects, but their selected prime provenance differs.
-/

namespace Integration.RiemannSSP15ExecutionDescentNoGo

namespace W := Integration.RiemannSSP15RHProducerSameGraphWeld
namespace SF := Integration.RiemannSSP15SignedFRACTRAN
namespace Codec := Integration.RiemannSSP15DepthFiveRoleCodec
namespace Grid := Integration.RiemannSSP15ChosenGridTransversality

theorem fibre_constancy_of_factorization
    {X Y Z : Type*} (execution : X → Y) (observable : X → Z)
    (decoder : Y → Z)
    (descends : ∀ x, observable x = decoder (execution x))
    {a b : X} (same : execution a = execution b) :
    observable a = observable b := by
  rw [descends a, descends b, same]

theorem distinct_observable_prevents_descent
    {X Y Z : Type*} (execution : X → Y) (observable : X → Z)
    {a b : X}
    (same : execution a = execution b)
    (different : observable a ≠ observable b) :
    ¬ ∃ decoder : Y → Z, ∀ x, observable x = decoder (execution x) := by
  rintro ⟨decoder, h⟩
  exact different (fibre_constancy_of_factorization execution observable decoder h same)

end Integration.RiemannSSP15ExecutionDescentNoGo
