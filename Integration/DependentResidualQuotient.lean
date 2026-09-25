import Integration.Kernel.Quotient

/-!
# Dependent residual quotients

Lean's older `Integration.ResidualQuotient` uses one fixed residual carrier.
Several Agda lanes now require the strictly more general shape

```
Residual : Coarse → Type
```

so that different coarse strata can carry different residual types without
padding them into one global product.

This file mirrors the generic architecture of
`DASHI.Core.DependentRecoverableProjectionExact`:

* `DependentResidualQuotient Rich Coarse`;
* exact code `Sigma q.Residual`;
* exact encode/decode reopening;
* injectivity of the exact code;
* every declared consumer descends through the exact code.

No domain semantics are introduced here.
-/

namespace Integration.DependentResidual

open Integration.Kernel.Quotient

universe u v w

structure DependentResidualQuotient (Rich : Type u) (Coarse : Type v) where
  Residual : Coarse → Type w
  project : Rich → Coarse
  residual : (x : Rich) → Residual (project x)
  reopen : (c : Coarse) → Residual c → Rich
  reopen_project : ∀ x, reopen (project x) (residual x) = x

namespace DependentResidualQuotient

variable {Rich : Type u} {Coarse : Type v}

abbrev Code (q : DependentResidualQuotient Rich Coarse) :=
  Sigma q.Residual

def encode (q : DependentResidualQuotient Rich Coarse) (x : Rich) : q.Code :=
  ⟨q.project x, q.residual x⟩

def decode (q : DependentResidualQuotient Rich Coarse) : q.Code → Rich
  | ⟨c,r⟩ => q.reopen c r

theorem decode_encode (q : DependentResidualQuotient Rich Coarse) (x : Rich) :
    q.decode (q.encode x) = x :=
  q.reopen_project x

theorem encode_injective (q : DependentResidualQuotient Rich Coarse) :
    Function.Injective q.encode := by
  intro x y h
  rw [← q.decode_encode x, ← q.decode_encode y, h]

/-- Exact dependent reopening is sufficient for every downstream consumer. -/
theorem every_consumer_descends
    (q : DependentResidualQuotient Rich Coarse)
    {Outcome : Type*} (consumer : Rich → Outcome) :
    DescendsThrough consumer q.encode :=
  ⟨fun code => consumer (q.decode code),
    fun x => congrArg consumer (q.decode_encode x)⟩

end DependentResidualQuotient

structure Boundary where
  residualTypeMayDependOnCoarseState : Bool
  exactReopeningOwned : Bool
  exactCodeInjective : Bool
  everyConsumerDescendsThroughExactCode : Bool
  paddingToUniformResidualRequired : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  residualTypeMayDependOnCoarseState := true
  exactReopeningOwned := true
  exactCodeInjective := true
  everyConsumerDescendsThroughExactCode := true
  paddingToUniformResidualRequired := false

end Integration.DependentResidual
