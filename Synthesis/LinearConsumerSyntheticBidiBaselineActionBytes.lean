import Synthesis.LinearConsumerSyntheticBidiBaselineAction

/-!
# Canonical baseline-action bytes

Serialize the fully concrete 924x8 Lean baseline action as one byte per row,
with bit `j` equal to block column `j`.  This is derived structurally from the
formal action object; no runtime digest, cross-prover identity, or CADO claim is
introduced here.
-/

namespace Synthesis

/-- Natural-number value of one row of the concrete baseline action. -/
def syntheticBidiBaselineActionRowNat (r : SyntheticBidiRows) : Nat :=
  ∑ j : SyntheticBidiBlock,
    if syntheticBidiBaselineAction r j = 1
    then 2 ^ j.val
    else 0

/-- Canonical row byte for the concrete baseline action. -/
def syntheticBidiBaselineActionRowByte (r : SyntheticBidiRows) : BitVec 8 :=
  BitVec.ofNat 8 (syntheticBidiBaselineActionRowNat r)

/-- Flattened canonical 924-byte representation; row index is byte index. -/
def syntheticBidiBaselineActionBytes (r : Fin 924) : BitVec 8 :=
  syntheticBidiBaselineActionRowByte r

@[simp]
theorem syntheticBidiBaselineActionBytes_apply (r : SyntheticBidiRows) :
    syntheticBidiBaselineActionBytes r = syntheticBidiBaselineActionRowByte r :=
  rfl

end Synthesis
