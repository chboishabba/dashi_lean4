import Welds.PNPResidualGeometryBridgeExact

namespace PNPDAGFrontierCapacity

-- An actual backward gate replacement: remove the demanded output
-- and add its distinct operands. Shared wires count once.
def replace {W : Type*} [DecidableEq W]
    (F : Finset W) (w : W) (operands : Finset W) :=
  F.erase w ∪ operands

theorem replacement_capacity {W : Type*} [DecidableEq W]
    (F : Finset W) (w : W) (operands : Finset W) (hw : w ∈ F) :
    (replace F w operands).card ≤ F.card+(operands.card-1) := by
  have h := Finset.card_union_le (F.erase w) operands
  have he := Finset.card_erase_of_mem hw
  have hp : 0<F.card := Finset.card_pos.mpr ⟨w,hw⟩
  unfold replace
  omega

inductive Trace {W : Type*} [DecidableEq W] :
    Finset W → Finset W → Nat → Prop where
  | done (F : Finset W) : Trace F F 0
  | step {F T : Finset W} {w : W} {operands : Finset W} {c : Nat}
      (hw : w∈F) (hf : operands.card≤2)
      (rest : Trace (replace F w operands) T c) :
      Trace F T ((operands.card-1)+c)

theorem trace_capacity {W : Type*} [DecidableEq W]
    {F T : Finset W} {c : Nat} (p : Trace F T c) :
    T.card ≤ F.card+c := by
  induction p with
  | done F => simp
  | step hw hf rest ih =>
    have h := replacement_capacity _ _ _ hw
    omega

-- Every essential input must occur in the actual final demand set.
-- The dependency-semantic theorem is already owned by the Agda
-- indexed sparse compiler. This is its finite cardinality receiver.
theorem essential_lower {W : Type*} [DecidableEq W]
    (out : W) (inputs essential : Finset W) (c : Nat)
    (trace : Trace ({out} : Finset W) inputs c)
    (h : essential ⊆ inputs) :
    essential.card ≤ 1+c := by
  have hp := trace_capacity trace
  have he := Finset.card_le_card h
  simp at hp
  omega

-- At most one unit per binary gate and no unit per unary/constant.
-- Distinct chronological gate IDs are needed to interpret the trace
-- as a subcount of original circuit gates, as the Python producer does.
-- Essential input count alone is at most input length, not S1's
-- missing superpolynomial semantic lower bound.
end PNPDAGFrontierCapacity
