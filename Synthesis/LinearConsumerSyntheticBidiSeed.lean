import Synthesis.LinearConsumerSyntheticBidiIncidence

/-!
# Exact deterministic synthetic bidi seed block

Mirror the `dashiRTX` baseline seed constructor used for the synthetic
Block-Wiedemann context.  The runtime uses 64-bit wraparound arithmetic:

    mix64(x):
      x ^= x >> 30
      x *= 0xbf58476d1ce4e5b9
      x ^= x >> 27
      x *= 0x94d049bb133111eb
      x ^= x >> 31

and block column `j` starts from

    BASEY xor (j << 32).

For matrix row `r`, the word index is `r / 64` and bit index is `r % 64`.
`BitVec 64` gives the same fixed-width multiplication/XOR/shift semantics on the
formal side.  This source does not itself prove cross-language identity with the
runtime block digest.
-/

namespace Synthesis

abbrev SyntheticBidiWord := BitVec 64

/-- Explicit wrap-to-64-bit conversion. -/
def syntheticBidiWordOfNat (n : Nat) : SyntheticBidiWord :=
  BitVec.ofNat 64 n

/-- Exact formal mirror of the runtime 64-bit mixer. -/
def syntheticBidiMix64 (x : SyntheticBidiWord) : SyntheticBidiWord :=
  let x₁ := x ^^^ (x >>> 30)
  let x₂ := x₁ * syntheticBidiWordOfNat 0xBF58476D1CE4E5B9
  let x₃ := x₂ ^^^ (x₂ >>> 27)
  let x₄ := x₃ * syntheticBidiWordOfNat 0x94D049BB133111EB
  x₄ ^^^ (x₄ >>> 31)

/-- Runtime `BASEY`. -/
def syntheticBidiBaseY : SyntheticBidiWord :=
  syntheticBidiWordOfNat 0x3C6EF372FE94F82B

/-- Word whose bits populate rows `64*w .. 64*w+63` of block column `j`. -/
def syntheticBidiSeedWord (j : SyntheticBidiBlock) (w : Nat) : SyntheticBidiWord :=
  let columnSeed :=
    syntheticBidiBaseY ^^^ (syntheticBidiWordOfNat j.val <<< 32)
  let wordSalt :=
    syntheticBidiWordOfNat 0x9E3779B97F4A7C15 *
      syntheticBidiWordOfNat (w + 1)
  syntheticBidiMix64 (columnSeed ^^^ wordSalt)

/-- Exact finite 924x8 seed block constructor mirrored from `build_block(BASEY)`. -/
def syntheticBidiSeedBlock :
    Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  fun r j =>
    if (syntheticBidiSeedWord j (r.val / 64)).getLsbD (r.val % 64)
    then 1
    else 0

@[simp]
theorem syntheticBidiSeedBlock_apply
    (r : SyntheticBidiRows) (j : SyntheticBidiBlock) :
    syntheticBidiSeedBlock r j =
      if (syntheticBidiSeedWord j (r.val / 64)).getLsbD (r.val % 64)
      then 1
      else 0 :=
  rfl

end Synthesis
