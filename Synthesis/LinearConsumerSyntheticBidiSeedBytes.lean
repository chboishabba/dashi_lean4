import Synthesis.LinearConsumerSyntheticBidiSeed

/-!
# Canonical deterministic seed-block bytes

The runtime serializes the 924x8 baseline seed block as one byte per row, with
bit `j` equal to column `j`.  This module derives the same representation
structurally from the already-formal seed generator; it does not copy 924 bytes.

No runtime digest, cross-prover equality, or production CADO identity is claimed
here.
-/

namespace Synthesis

/-- Natural-number value of one row of the deterministic 924x8 seed block. -/
def syntheticBidiSeedRowNat (r : SyntheticBidiRows) : Nat :=
  ∑ j : SyntheticBidiBlock,
    if (syntheticBidiSeedWord j (r.val / 64)).getLsbD (r.val % 64)
    then 2 ^ j.val
    else 0

/-- Canonical row byte: bit `j` is the formal seed-block entry `(r,j)`. -/
def syntheticBidiSeedRowByte (r : SyntheticBidiRows) : BitVec 8 :=
  BitVec.ofNat 8 (syntheticBidiSeedRowNat r)

/-- Flattened canonical 924-byte representation; the row index is the byte index. -/
def syntheticBidiSeedBytes (r : Fin 924) : BitVec 8 :=
  syntheticBidiSeedRowByte r

@[simp]
theorem syntheticBidiSeedBytes_apply (r : SyntheticBidiRows) :
    syntheticBidiSeedBytes r = syntheticBidiSeedRowByte r :=
  rfl

end Synthesis
