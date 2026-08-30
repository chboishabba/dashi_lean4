import Integration.Levels
import Synthesis.ToneCore
import Cuisine.SupervoxelClopen

/-!
# The ternary hub: one carrier behind six of the corpus's ternary vocabularies

The corpus introduces a three-element carrier independently in at least six
places, each with its own constructor names, its own polarity map, and no stated
relation to the others:

| Agda source | carrier | polarity map |
| --- | --- | --- |
| `DASHI/Algebra/Trit.agda` | `Trit = neg ∣ zer ∣ pos` | `inv` |
| `Base369.agda` | `TriTruth = tri-low ∣ tri-mid ∣ tri-high` | (only `rotateTri`) |
| `DASHI/Foundations/SSPTritCarrier.agda` | `SSPTrit` | (none; polarity is a *classifier*) |
| `DASHI/Geometry/SSP369Ultrametric.agda` | `Digit369 = digit3 ∣ digit6 ∣ digit9` | `invert369` (in the codec bridge) |
| `DASHI/Codec/TriadicMaskSign.agda` | `TritCode` (a mask bit + a gated sign) | `invertTrit` via the codec |
| `DASHI/Foundations/ConstraintClopenRefinement.agda` | `BTBranch` | (none) |

`Synthesis.ToneCore` already identifies the first two and puts them in bijection
with `ZMod 3`, and `Cuisine.SupervoxelClopen` identifies `BTBranch` with `Trit`.
This file completes the picture and, more importantly, fixes the *coordinate* in
which the identifications are stated, which is where the corpus is inconsistent
with itself.

## Balanced coordinates

Every one of these carriers has a distinguished *neutral* value (`zer`,
`tri-mid`, `sspZero`, `digit6`, the inactive mask code, `zeroBranch`) and a
polarity swap exchanging the other two.  The **balanced coordinate** is the
unique bijection to `ZMod 3` sending the neutral value to `0` and turning every
one of the corpus's polarity maps into negation:

* `bal_inv`, `balTone_reflect`, `balDigit_invert369`, `balCode_invert` — the
  equivariance statements, one per carrier;
* `neutral_forced` — any inversion-equivariant map into `ZMod 3` *must* send the
  neutral value to `0`, so the coordinate is not a convention;
* `sign_forced`, `bal_unique_up_to_sign` — the remaining freedom is exactly the
  sign choice, so there are precisely two admissible coordinates and they differ
  by negation.

## The recorded incompatibility

`Base369`'s ternary XOR is *not* addition in these coordinates: its neutral
element is `tri-low`, i.e. the balanced digit `-1`, so
`balTone (triXor a b) = balTone a + balTone b + 1` (`balTone_triXor_affine`).
The two ternary operations the corpus uses therefore agree only up to a
translation.  This was observed for the depth-15 fibre in
`Synthesis.CodecBridge`; here it is the digit-level statement, and it is the
reason the hub is stated with an explicit choice of coordinate.

Every identification below is a `Levels.Transport`, i.e. a level-4 witness.
Nothing here is a claim about anything but three-element sets.
-/

namespace Integration.TernaryHub

open Integration.Levels
open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth triXor rotateTri)
open Synthesis.ToneCore (triReflect)

/-! ## Carriers not previously mirrored -/

/-- Mirror of `DASHI.Geometry.SSP369Ultrametric.Digit369`. -/
inductive Digit369 | d3 | d6 | d9
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `DASHI.Codec.TriadicPAdicCodec369Bridge.invert369`. -/
def invert369 : Digit369 → Digit369
  | .d3 => .d9 | .d6 => .d6 | .d9 => .d3

/-- Mirror of `DASHI.Foundations.SSPTritCarrier.SSPTrit`. -/
inductive SSPTrit | negOne | zero | posOne
  deriving DecidableEq, Repr, Fintype

/-- The polarity swap on `SSPTrit`.  The Agda module supplies only the
*classifiers* `sspTritPolarity` / `sspTritNeutrality`, never this map; it is
introduced here so that the carrier can be compared with the others at level 4,
and the comparison below is what justifies calling it "the" polarity swap. -/
def sspTritInv : SSPTrit → SSPTrit
  | .negOne => .posOne | .zero => .zero | .posOne => .negOne

/-- Mirror of `DASHI.Codec.TriadicMaskSign.Bit`. -/
inductive Bit | off | on
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `DASHI.Codec.TriadicMaskSign.Sign`. -/
inductive Sign | minus | plus
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `DASHI.Codec.TriadicMaskSign.ActiveSign`: a sign is carried only
where the support mask is on. -/
def ActiveSign : Bit → Type
  | .off => Unit
  | .on => Sign

instance : ∀ b, DecidableEq (ActiveSign b)
  | .off => inferInstanceAs (DecidableEq Unit)
  | .on => inferInstanceAs (DecidableEq Sign)

/-- Mirror of `DASHI.Codec.TriadicMaskSign.TritCode`: one support bit plus
exactly one gated sign. -/
structure TritCode where
  /-- Support bit. -/
  active : Bit
  /-- The sign, present only when the support bit is on. -/
  sign : ActiveSign active

/-- Mirror of `TriadicMaskSign.encodeTrit`. -/
def encodeTrit : Trit → TritCode
  | .neg => ⟨.on, .minus⟩
  | .zer => ⟨.off, ()⟩
  | .pos => ⟨.on, .plus⟩

/-- Mirror of `TriadicMaskSign.decodeTrit`. -/
def decodeTrit : TritCode → Trit
  | ⟨.off, _⟩ => .zer
  | ⟨.on, .minus⟩ => .neg
  | ⟨.on, .plus⟩ => .pos

theorem decode_encode (t : Trit) : decodeTrit (encodeTrit t) = t := by
  cases t <;> rfl

theorem encode_decode (c : TritCode) : encodeTrit (decodeTrit c) = c := by
  obtain ⟨b, s⟩ := c
  cases b with
  | off => rfl
  | on => cases s <;> rfl

/-- The mask/sign representation is the balanced-ternary digit. -/
def codeEquivTrit : TritCode ≃ Trit where
  toFun := decodeTrit
  invFun := encodeTrit
  left_inv := encode_decode
  right_inv := decode_encode

/-- Sign inversion on the codec representation, mirroring
`TriadicMaskSign.invertSign` gated by the support bit. -/
def invertCode : TritCode → TritCode
  | ⟨.off, _⟩ => ⟨.off, ()⟩
  | ⟨.on, .minus⟩ => ⟨.on, .plus⟩
  | ⟨.on, .plus⟩ => ⟨.on, .minus⟩

/-! ## Balanced coordinates -/

/-- Balanced coordinate of a digit: `neg ↦ -1`, `zer ↦ 0`, `pos ↦ 1`. -/
def balTrit : Trit → ZMod 3
  | .neg => -1 | .zer => 0 | .pos => 1

/-- Balanced coordinate of a `Base369` tone.  Note that this is *not*
`Synthesis.ToneCore.toneToZMod`, which uses the XOR-index coordinate; the two
differ by the translation recorded in `balTone_eq_toneToZMod_sub_one`. -/
def balTone : TriTruth → ZMod 3
  | .low => -1 | .mid => 0 | .high => 1

/-- Balanced coordinate of a 3/6/9 address digit. -/
def balDigit : Digit369 → ZMod 3
  | .d3 => -1 | .d6 => 0 | .d9 => 1

/-- Balanced coordinate of the SSP trit carrier. -/
def balSSP : SSPTrit → ZMod 3
  | .negOne => -1 | .zero => 0 | .posOne => 1

/-- Balanced coordinate of the codec mask/sign representation. -/
def balCode (c : TritCode) : ZMod 3 := balTrit (decodeTrit c)

/-- Balanced coordinate of the clopen-refinement branch type. -/
def balBranch : Cuisine.SupervoxelClopen.BTBranch → ZMod 3
  | .negativeBranch => -1 | .zeroBranch => 0 | .positiveBranch => 1

/-- Inverse of the balanced coordinate on digits. -/
def unbalTrit (z : ZMod 3) : Trit := if z = 0 then .zer else if z = 1 then .pos else .neg

/-- Each balanced coordinate is a bijection. -/
def balTritEquiv : Trit ≃ ZMod 3 where
  toFun := balTrit
  invFun := unbalTrit
  left_inv := by decide
  right_inv := by decide

def balToneEquiv : TriTruth ≃ ZMod 3 where
  toFun := balTone
  invFun := fun z => if z = 0 then .mid else if z = 1 then .high else .low
  left_inv := by decide
  right_inv := by decide

def balDigitEquiv : Digit369 ≃ ZMod 3 where
  toFun := balDigit
  invFun := fun z => if z = 0 then .d6 else if z = 1 then .d9 else .d3
  left_inv := by decide
  right_inv := by decide

def balSSPEquiv : SSPTrit ≃ ZMod 3 where
  toFun := balSSP
  invFun := fun z => if z = 0 then .zero else if z = 1 then .posOne else .negOne
  left_inv := by decide
  right_inv := by decide

def balCodeEquiv : TritCode ≃ ZMod 3 := codeEquivTrit.trans balTritEquiv

def balBranchEquiv : Cuisine.SupervoxelClopen.BTBranch ≃ ZMod 3 where
  toFun := balBranch
  invFun := fun z => if z = 0 then .zeroBranch else if z = 1 then .positiveBranch
    else .negativeBranch
  left_inv := by decide
  right_inv := by decide

/-! ## Every corpus polarity map is negation in balanced coordinates -/

theorem balTrit_inv (t : Trit) : balTrit (Trit.inv t) = - balTrit t := by
  cases t <;> decide

theorem balTone_reflect (t : TriTruth) : balTone (triReflect t) = - balTone t := by
  cases t <;> decide

theorem balDigit_invert369 (d : Digit369) : balDigit (invert369 d) = - balDigit d := by
  cases d <;> decide

theorem balSSP_inv (s : SSPTrit) : balSSP (sspTritInv s) = - balSSP s := by
  cases s <;> decide

theorem balCode_invert (c : TritCode) : balCode (invertCode c) = - balCode c := by
  obtain ⟨b, s⟩ := c
  cases b with
  | off => cases s; decide
  | on => cases s <;> decide

/-! ## The hub, as level-4 transports -/

/-- Negation on `ZMod 3`: the hub's distinguished operation. -/
def zneg : ZMod 3 → ZMod 3 := fun z => -z

/-- `Trit` with digit negation *is* `ZMod 3` with negation. -/
def tritHub : Transport Trit (ZMod 3) Trit.inv zneg := ⟨balTritEquiv, balTrit_inv⟩

/-- The `Base369` tone with the reflection induced by digit negation. -/
def toneHub : Transport TriTruth (ZMod 3) triReflect zneg := ⟨balToneEquiv, balTone_reflect⟩

/-- The 3/6/9 address digit with the codec bridge's `invert369`. -/
def digitHub : Transport Digit369 (ZMod 3) invert369 zneg := ⟨balDigitEquiv, balDigit_invert369⟩

/-- The SSP trit carrier with its polarity swap. -/
def sspHub : Transport SSPTrit (ZMod 3) sspTritInv zneg := ⟨balSSPEquiv, balSSP_inv⟩

/-- The codec mask/sign representation with gated sign inversion. -/
def codeHub : Transport TritCode (ZMod 3) invertCode zneg := ⟨balCodeEquiv, balCode_invert⟩

/-- Composite: the codec representation is the `Base369` tone, polarity and all. -/
def codeToneTransport : Transport TritCode TriTruth invertCode triReflect :=
  codeHub.trans toneHub.symm

/-- Composite: the 3/6/9 address digit is the balanced-ternary digit. -/
def digitTritTransport : Transport Digit369 Trit invert369 Trit.inv :=
  digitHub.trans tritHub.symm

/-- The composite `Digit369 → Trit` is exactly the inverse of the corpus's own
`trit→369` of `DASHI.Codec.TriadicPAdicCodec369Bridge` (`neg ↦ 3, zer ↦ 6,
pos ↦ 9`), so the hub reproduces the supplied map rather than inventing one. -/
def trit369 : Trit → Digit369
  | .neg => .d3 | .zer => .d6 | .pos => .d9

theorem digitTritTransport_eq_trit369_symm (t : Trit) :
    digitTritTransport.map (trit369 t) = t := by
  cases t <;> decide

/-- The supplied `trit→369` is itself polarity-equivariant, as the Agda states
(`trit→369-inversion`). -/
theorem trit369_inv (t : Trit) : trit369 (Trit.inv t) = invert369 (trit369 t) := by
  cases t <;> rfl

/-- Composite: the clopen-refinement branch type is the same carrier.  The Agda
gives `BTBranch` no operations at all, so this is the strongest statement the
source supports at that node: a bijection, promoted to level 4 only by *choosing*
the polarity swap that matches. -/
def branchTritEquiv : Cuisine.SupervoxelClopen.BTBranch ≃ Trit :=
  balBranchEquiv.trans balTritEquiv.symm

theorem branchTritEquiv_eq_supplied (b : Cuisine.SupervoxelClopen.BTBranch) :
    branchTritEquiv b = Cuisine.SupervoxelClopen.btBranchEquivTrit b := by
  cases b <;> decide

/-! ## The coordinate is forced, up to sign -/

/-- Any map into `ZMod 3` that turns digit negation into negation must send the
neutral digit to `0`.  No injectivity is needed: `2` is invertible in `ZMod 3`. -/
theorem neutral_forced (f : Trit → ZMod 3) (h : ∀ t, f (Trit.inv t) = - f t) :
    f .zer = 0 := by
  have key : ∀ z : ZMod 3, z = -z → z = 0 := by decide
  exact key _ (h .zer)

/-- For a *bijective* coordinate the remaining freedom is exactly the sign of
the positive digit, and the negative digit is then determined. -/
theorem sign_forced (e : Trit ≃ ZMod 3) (h : ∀ t, e (Trit.inv t) = - e t) :
    e .zer = 0 ∧ (e .pos = 1 ∨ e .pos = -1) ∧ e .neg = - e .pos := by
  refine ⟨neutral_forced e h, ?_, ?_⟩
  · have hne : e .pos ≠ 0 := by
      intro hp
      exact absurd (e.injective (hp.trans (neutral_forced e h).symm)) (by decide)
    have key : ∀ z : ZMod 3, z ≠ 0 → z = 1 ∨ z = -1 := by decide
    exact key _ hne
  · have := h .pos
    simpa [Trit.inv] using this

/-- Hence there are exactly two admissible balanced coordinates on the ternary
hub, and they differ by negation. -/
theorem bal_unique_up_to_sign (e : Trit ≃ ZMod 3) (h : ∀ t, e (Trit.inv t) = - e t) :
    (∀ t, e t = balTrit t) ∨ (∀ t, e t = - balTrit t) := by
  obtain ⟨hz, hp, hn⟩ := sign_forced e h
  rcases hp with hp | hp
  · left; intro t; cases t
    · simpa [balTrit, hp] using hn
    · simpa [balTrit] using hz
    · simpa [balTrit] using hp
  · right; intro t; cases t
    · simpa [balTrit, hp] using hn
    · simpa [balTrit] using hz
    · simpa [balTrit] using hp

/-! ## The recorded incompatibility: `Base369` XOR is affine, not additive -/

/-- The `Base369` index coordinate and the balanced coordinate differ by one. -/
theorem balTone_eq_toneToZMod_sub_one (t : TriTruth) :
    balTone t = Synthesis.ToneCore.toneToZMod t - 1 := by
  cases t <;> decide

/-- In balanced coordinates the corpus's ternary XOR is the affine law
`x + y + 1`, not addition: its neutral element is the digit `-1`. -/
theorem balTone_triXor_affine (a b : TriTruth) :
    balTone (triXor a b) = balTone a + balTone b + 1 := by
  cases a <;> cases b <;> decide

/-- Consequently XOR is *not* the group law of the balanced coordinate: there is
no way to read `triXor` as `ZMod 3` addition through `balTone`. -/
theorem balTone_triXor_ne_add : ∃ a b : TriTruth,
    balTone (triXor a b) ≠ balTone a + balTone b := ⟨.mid, .mid, by decide⟩

/-- The rotation, by contrast, *is* `+1` in balanced coordinates too — the
translation cancels. -/
theorem balTone_rotate (t : TriTruth) : balTone (rotateTri t) = balTone t + 1 := by
  cases t <;> decide

/-! ## The hub as a checked bundle -/

/-- All six ternary carriers of the corpus, each with a checked level-4
transport onto `ZMod 3` with negation. -/
structure TernaryHubBundle where
  /-- `DASHI.Algebra.Trit`. -/
  trit : Transport Trit (ZMod 3) Trit.inv zneg
  /-- `Base369.TriTruth`. -/
  tone : Transport TriTruth (ZMod 3) triReflect zneg
  /-- `DASHI.Geometry.SSP369Ultrametric.Digit369`. -/
  digit : Transport Digit369 (ZMod 3) invert369 zneg
  /-- `DASHI.Foundations.SSPTritCarrier.SSPTrit`. -/
  ssp : Transport SSPTrit (ZMod 3) sspTritInv zneg
  /-- `DASHI.Codec.TriadicMaskSign.TritCode`. -/
  code : Transport TritCode (ZMod 3) invertCode zneg
  /-- `DASHI.Foundations.ConstraintClopenRefinement.BTBranch`, bijection only. -/
  branch : Cuisine.SupervoxelClopen.BTBranch ≃ ZMod 3
  /-- The supplied `trit→369` agrees with the hub. -/
  supplied369 : ∀ t, trit369 (Trit.inv t) = invert369 (trit369 t)
  /-- The supplied `BTBranch ≃ Trit` agrees with the hub. -/
  suppliedBranch : ∀ b, branchTritEquiv b = Cuisine.SupervoxelClopen.btBranchEquivTrit b
  /-- The coordinate is forced up to sign. -/
  coordinateForced : ∀ e : Trit ≃ ZMod 3, (∀ t, e (Trit.inv t) = - e t) →
    (∀ t, e t = balTrit t) ∨ (∀ t, e t = - balTrit t)
  /-- …and `Base369` XOR is affine in it, so the two ternary operations of the
  corpus are not the same group law. -/
  xorAffine : ∀ a b, balTone (triXor a b) = balTone a + balTone b + 1

/-- The checked inhabitant. -/
def ternaryHub : TernaryHubBundle where
  trit := tritHub
  tone := toneHub
  digit := digitHub
  ssp := sspHub
  code := codeHub
  branch := balBranchEquiv
  supplied369 := trit369_inv
  suppliedBranch := branchTritEquiv_eq_supplied
  coordinateForced := bal_unique_up_to_sign
  xorAffine := balTone_triXor_affine

end Integration.TernaryHub
