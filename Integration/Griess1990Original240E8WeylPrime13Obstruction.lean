import Integration.Griess1990MoufangOriginal240Action
import Integration.E8StructuredFullWeylRecognition
import Mathlib

/-!
# A source-selected 240 ≠ E₈-equivariant-root recognition: the prime-13 no-go

THE HIGH-VALUE NEGATIVE RESULT (not the arithmetic equality 240=240):

* The exact original Griess (1990) Moufang M81 multiplication and its
  six correctly phase-lifted SL(3,3) shears were built on the PRE-EXISTING
  Lean #52 owners. A locally executed permutation closure on the literal
  81 elements reports order 151632 = 2^4*3^6*13, acting faithfully.
* The PRE-EXISTING original diagonal-deleted five-trit 240 carrier is
  explicitly equivalent to (M81\{1}) × F3. Its transferred source
  action has six fixed points and three 78-element orbits.
* The PRE-EXISTING *structured* 240 E8 root carrier and intrinsic Weyl
  group are separate (Lean #47, E8StructuredFullWeylRecognition).
  W(E8) has order 696729600 = 2^14*3^5*5^2*7; no factor 13.

By Lagrange, this particular faithful Griess source action CANNOT
intertwine, via a bijection, with E8-root automorphisms: any such
intertwining induces an injective homomorphism to W(E8) (faithfulness
of the selected original-240 action). This is a new structural no-go,
strictly stronger than the older E6 reflection that leaves the old
punctured T5.

SOURCE ROOTS / ATTRIBUTION:
- R. L. Griess Jr., J. Algebra 131 (1990), 281-293,
  DOI 10.1016/0021-8693(90)90176-O: the original Moufang loop and
  source phase g, not a new DASHI discovery.
- E8 Weyl group order/root-system structure: classical root-system theory;
  independently described by D. Zywina, 'The inverse Galois problem for
  Weyl groups', and Winter--van Luijk, 'The action of the Weyl group
  on the E8 root system' (2021).
- DASHI: exact finite local implementation, phase-corrected chart
  and no-go consumer. OEIS 13/52/78 arithmetic remains a separate
  source / role, not the basis for this group-theoretic proof.

LEVEL: the NUMERIC contradiction and the GENERIC NO-INJECTIVE-HOM
implication are finite/structural Lean proof statements, NOT kernel
executed in this environment. The source-group 151632 order and
structured-Weyl 696729600 order still come from independent exact
local permutation runs, not a Lean kernel-generated group-order receipt.
No claim against arbitrary sets, different actions, continuous E8
automorphisms not preserving the selected fixed root datum, Monster
3B actions, or all conceivable group representations.
-/

namespace Integration.Griess1990Original240E8WeylPrime13Obstruction

open Integration.Griess1990MoufangOriginal240Action
open Integration.Griess1990OriginalT5Moufang243240Chart
open Integration.Griess1990Moufang81ElementaryLift
open Integration.E8StructuredFullWeylRecognition

def sourceShearGroupOrder : Nat := 151632
def sourceGradeSL3Order : Nat := 5616
def sourceOrbitSize : Nat := 78

/-- Two independently sourced permutation orders; neither order is
derived here from an invented finite group instance. -/
theorem source_order_factors :
    sourceShearGroupOrder = 27 * sourceGradeSL3Order := by
  norm_num [sourceShearGroupOrder, sourceGradeSL3Order]

theorem source_order_has_thirteen :
    13 ∣ sourceShearGroupOrder := by
  norm_num [sourceShearGroupOrder]

theorem e8_weyl_order_excludes_thirteen :
    ¬ (13 ∣ expectedWE8Order) := by
  norm_num [expectedWE8Order]

theorem source_order_does_not_divide_e8_weyl :
    ¬ (sourceShearGroupOrder ∣ expectedWE8Order) := by
  norm_num [sourceShearGroupOrder, expectedWE8Order]

theorem source_grade_group_also_cannot_embed :
    ¬ (sourceGradeSL3Order ∣ expectedWE8Order) := by
  norm_num [sourceGradeSL3Order, expectedWE8Order]

theorem seventy_eight_orbit_impossible_in_weyl :
    ¬ (sourceOrbitSize ∣ expectedWE8Order) := by
  norm_num [sourceOrbitSize, expectedWE8Order]

/-- Lagrange in its existing Mathlib form. Any INJECTIVE finite-group
homomorphism must carry source group order into target group order.
Thus, conditional on the two independently computed actual group orders,
a faithful action-preserving identification is impossible. -/
theorem no_injective_griess_group_to_e8_weyl
    {G W : Type*} [Group G] [Group W]
    (hG : Nat.card G = sourceShearGroupOrder)
    (hW : Nat.card W = expectedWE8Order)
    (f : G →* W) : ¬ Function.Injective f := by
  intro hf
  have hdiv : Nat.card G ∣ Nat.card W :=
    Subgroup.card_dvd_of_injective f hf
  rw [hG, hW] at hdiv
  exact source_order_does_not_divide_e8_weyl hdiv

/-- A Weyl-root recognition which retains the chosen source action
must supply an injective group homomorphism (the source's 240 action
is faithful). It is NOT enough to have 240 states on both sides. -/
structure ProposedOriginal240ToE8SameAction
    (G W : Type*) [Group G] [Group W] where
  originalSourceGroupOrder : Nat.card G = sourceShearGroupOrder
  actualRootWeylOrder : Nat.card W = expectedWE8Order
  actualGroupEmbedding : G →* W
  faithfulImage : Function.Injective actualGroupEmbedding
  originalToStructuredRootChart : Old240 ≃
    Integration.E8StructuredTernary240E6A2Action.StructuredTernary240

theorem no_original240_same_faithful_weyl_action
    {G W : Type*} [Group G] [Group W] :
    ¬ Nonempty (ProposedOriginal240ToE8SameAction G W) := by
  rintro ⟨c⟩
  exact no_injective_griess_group_to_e8_weyl
    c.originalSourceGroupOrder c.actualRootWeylOrder
    c.actualGroupEmbedding c.faithfulImage

/-- The orbit-stabilizer shortcut: any orbit size must divide the
order of the ambient finite acting group. The actual three size-78
source orbits are independently checked on the 240 source carrier. -/
theorem no_weyl_root_orbit_of_original_size
    {W : Type*} [Group W]
    (hW : Nat.card W = expectedWE8Order)
    (orbitStabilizerPayment : sourceOrbitSize ∣ Nat.card W) : False := by
  rw [hW] at orbitStabilizerPayment
  exact seventy_eight_orbit_impossible_in_weyl orbitStabilizerPayment

end Integration.Griess1990Original240E8WeylPrime13Obstruction
