import Mathlib

namespace TimesFM3

abbrev Series (d t : Nat) := Fin d → Fin t → ℝ
abbrev QuantileSeries (d h : Nat) := Fin d → Fin h → Fin 9 → ℝ

structure World (d p q t h : Nat) where
  targets : Series d (t + h)
  pastCovariates : Series p (t + h)
  knownCovariates : Series q (t + h)

structure Observation (d p q t h : Nat) where
  targets : Series d t
  pastCovariates : Series p t
  knownCovariates : Series q (t + h)

structure Forecast (d h : Nat) where
  point : Series d h
  quantile : QuantileSeries d h

def observe {d p q t h : Nat} (w : World d p q t h) :
    Observation d p q t h where
  targets := fun i j => w.targets i ⟨j.val, Nat.lt_add_right h j.isLt⟩
  pastCovariates := fun i j =>
    w.pastCovariates i ⟨j.val, Nat.lt_add_right h j.isLt⟩
  knownCovariates := w.knownCovariates

def AvailableEq {d p q t h : Nat}
    (a b : World d p q t h) : Prop := observe a = observe b

def liftPredictor {d p q t h : Nat}
    (predict : Observation d p q t h → Forecast d h) :
    World d p q t h → Forecast d h := predict ∘ observe

theorem no_future_target_leakage {d p q t h : Nat}
    (predict : Observation d p q t h → Forecast d h)
    (a b : World d p q t h)
    (hab : AvailableEq a b) :
    liftPredictor predict a = liftPredictor predict b :=
  congrArg predict hab

def TemporalAllowed {d n : Nat} (a b : Fin d × Fin n) : Prop :=
  a.1 = b.1 ∧ b.2.val ≤ a.2.val

def VariateAllowed {d n : Nat} (a b : Fin d × Fin n) : Prop :=
  a.2 = b.2

theorem temporal_causal {d n : Nat}
    (a b : Fin d × Fin n) (h : TemporalAllowed a b) :
    b.2.val ≤ a.2.val := h.2

theorem variate_same_patch {d n : Nat}
    (a b : Fin d × Fin n) (h : VariateAllowed a b) :
    a.2 = b.2 := h

abbrev Patches (d n : Nat) := Fin d → Fin n → Fin 32 → ℝ

def patch (x : Patches d n) : Patches d n := x
def unpatch (x : Patches d n) : Patches d n := x

theorem patch_roundtrip {d n : Nat} (x : Patches d n) :
    unpatch (patch x) = x := rfl

def maskUnknown (value : ℝ) (available : Bool) : ℝ :=
  if available then value else 0

theorem masked_unknown_independent (x y : ℝ) :
    maskUnknown x false = maskUnknown y false := rfl

theorem masked_known_identity (x : ℝ) :
    maskUnknown x true = x := rfl

def QuantileOrdered {d h : Nat} (f : Forecast d h) : Prop :=
  ∀ i j a b, a.val ≤ b.val →
    f.quantile i j a ≤ f.quantile i j b

structure CoherentPredictor (d p q t h : Nat) where
  run : Observation d p q t h → Forecast d h
  coherent : ∀ x, QuantileOrdered (run x)

theorem coherent_prediction {d p q t h : Nat}
    (model : CoherentPredictor d p q t h)
    (w : World d p q t h) :
    QuantileOrdered (liftPredictor model.run w) :=
  model.coherent (observe w)

theorem coherent_no_leakage {d p q t h : Nat}
    (model : CoherentPredictor d p q t h)
    (a b : World d p q t h)
    (hab : AvailableEq a b) :
    liftPredictor model.run a = liftPredictor model.run b :=
  no_future_target_leakage model.run a b hab

end TimesFM3
