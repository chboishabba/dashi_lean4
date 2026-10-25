import Integration.EisensteinChoiceRecoveryExact

namespace Dashi.EisensteinChoiceRecoveryValidation

open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinChoiceRepresentativeExact
open Dashi.EisensteinChoiceRecoveryExact

/-- Regression contract: the canonical norm-n representative must recover
exactly the split-exponent choice that constructed it. -/
example
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c : SplitChoice n) :
    splitChoiceOfRepresentation
        (choiceRepresentative n H c) n hn
        (choiceRepresentative_norm n hn H c)
      = c :=
  splitChoice_choiceRepresentative n hn H c

/-- Regression contract: canonical representatives for distinct split choices
cannot be associated. -/
example
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c d : SplitChoice n) (hcd : c ≠ d) :
    ¬ Associated (choiceRepresentative n H c) (choiceRepresentative n H d) :=
  choiceRepresentative_not_associated_of_ne n hn H c d hcd

end Dashi.EisensteinChoiceRecoveryValidation
