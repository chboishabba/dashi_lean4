import Integration.TernaryHub

/-!
# Base369 as three cyclic groups, and which of its projections actually split

`Base369.agda` is the corpus's most widely imported non-prelude module (140
direct importers in the Agda cutset).  It defines three "truth universes"
`TriTruth`, `HexTruth`, `NonaryTruth` with an iterated rotation `spin`, a
rotation `rotate_`, a "spin XOR" and a "closed XOR", and proves that the two
XORs agree, that the rotation has the expected order, and that the XOR has a
left identity (plus associativity in the ternary case).  It never says what the
three universes *are*, nor how they are related to each other.

They are `ℤ/3`, `ℤ/6` and `ℤ/9`, and the XOR is addition:

* `triIdx_xor`, `hexIdx_xor`, `nonIdx_xor` — the index coordinate is an additive
  isomorphism in each of the three cases (`triAddEquiv`, `hexAddEquiv`,
  `nonAddEquiv`);
* `rotate_eq_succ` — the rotation is `+1`, in all three.

`DialecticalJourneyLoom.agda` tags the corpus's projections of this material as
`projection2x3`, `projection2x9` and `projectionThreeStrand`.  The first two are
factorisation claims, and they behave completely differently:

* **`projection2x3` is a theorem** — `hexSplit : HexTruth ≃+ ZMod 2 × ZMod 3`,
  the Chinese remainder splitting of `ℤ/6`, so the hexadic layer really is the
  ternary layer times a parity bit, and `hexSplit_snd_eq_triIdx_of_rotate`
  identifies its ternary component with the `Base369` ternary layer itself.
* **`projection2x9` has no carrier** — there is no eighteen-element universe in
  `Base369`; the tag names a projection of an object the module never defines.
  Recorded as an absence, not bridged.
* **The nonary layer does not factor as two ternary layers.**  `ℤ/9` has an
  element of order 9 and `ℤ/3 × ℤ/3` does not, so `nonary_not_ternary_square`:
  there is *no* additive isomorphism `NonaryTruth ≃+ TriTruth × TriTruth`, and
  indeed no bijection at all carrying `nonaryXor` to the componentwise
  `triXor`.  A base-3 digit *bijection* does exist (`nonaryDigits`), so this
  junction sits at level 3 and provably not at level 4.  The precise structure is
  `nonary_extension`: the nonary layer is a non-split extension of the ternary
  layer by itself, via the order-3 subgroup `triInNonary` and the reduction
  `nonaryReduce`.

Boundary: all six carriers here are finite cyclic groups of order at most 9.
Nothing about 3-6-9 numerology, physics or "vortex mathematics" is claimed; the
content is exactly the group theory stated above.
-/

namespace Integration.Base369Group

open AgdaMirror.Base369

instance : Fintype HexTruth :=
  ⟨{.h0, .h1, .h2, .h3, .h4, .h5}, fun x => by cases x <;> decide⟩

instance : Fintype NonaryTruth :=
  ⟨{.n0, .n1, .n2, .n3, .n4, .n5, .n6, .n7, .n8}, fun x => by cases x <;> decide⟩

/-! ## The three index coordinates -/

/-- `TriTruth` in its XOR-index coordinate (`tri-low ↦ 0`). -/
def triIdx : TriTruth → ZMod 3
  | .low => 0 | .mid => 1 | .high => 2

/-- `HexTruth` in its XOR-index coordinate. -/
def hexIdx : HexTruth → ZMod 6
  | .h0 => 0 | .h1 => 1 | .h2 => 2 | .h3 => 3 | .h4 => 4 | .h5 => 5

/-- `NonaryTruth` in its XOR-index coordinate. -/
def nonIdx : NonaryTruth → ZMod 9
  | .n0 => 0 | .n1 => 1 | .n2 => 2 | .n3 => 3 | .n4 => 4
  | .n5 => 5 | .n6 => 6 | .n7 => 7 | .n8 => 8

/-- The ternary universe *is* `ℤ/3`. -/
def triEquiv : TriTruth ≃ ZMod 3 where
  toFun := triIdx
  invFun := fun z => if z = 0 then .low else if z = 1 then .mid else .high
  left_inv := by decide
  right_inv := by decide

/-- The hexadic universe *is* `ℤ/6`. -/
def hexEquiv : HexTruth ≃ ZMod 6 where
  toFun := hexIdx
  invFun := fun z =>
    if z = 0 then .h0 else if z = 1 then .h1 else if z = 2 then .h2
    else if z = 3 then .h3 else if z = 4 then .h4 else .h5
  left_inv := by decide
  right_inv := by decide

/-- The nonary universe *is* `ℤ/9`. -/
def nonEquiv : NonaryTruth ≃ ZMod 9 where
  toFun := nonIdx
  invFun := fun z =>
    if z = 0 then .n0 else if z = 1 then .n1 else if z = 2 then .n2
    else if z = 3 then .n3 else if z = 4 then .n4 else if z = 5 then .n5
    else if z = 6 then .n6 else if z = 7 then .n7 else .n8
  left_inv := by decide
  right_inv := by decide

/-! ## The XORs are addition and the rotations are `+1` -/

theorem triIdx_xor (a b : TriTruth) : triIdx (triXor a b) = triIdx a + triIdx b := by
  cases a <;> cases b <;> decide

theorem hexIdx_xor (a b : HexTruth) : hexIdx (hexXor a b) = hexIdx a + hexIdx b := by
  cases a <;> cases b <;> decide

theorem nonIdx_xor (a b : NonaryTruth) : nonIdx (nonaryXor a b) = nonIdx a + nonIdx b := by
  cases a <;> cases b <;> decide

theorem triIdx_rotate (t : TriTruth) : triIdx (rotateTri t) = triIdx t + 1 := by
  cases t <;> decide

theorem hexIdx_rotate (h : HexTruth) : hexIdx (rotateHex h) = hexIdx h + 1 := by
  cases h <;> decide

theorem nonIdx_rotate (n : NonaryTruth) : nonIdx (rotateNonary n) = nonIdx n + 1 := by
  cases n <;> decide

/-- The three universes as additive groups. -/
def triAddEquiv : TriTruth ≃ ZMod 3 := triEquiv
/-- See `hexIdx_xor`: this bijection carries `hexXor` to addition. -/
def hexAddEquiv : HexTruth ≃ ZMod 6 := hexEquiv
/-- See `nonIdx_xor`: this bijection carries `nonaryXor` to addition. -/
def nonAddEquiv : NonaryTruth ≃ ZMod 9 := nonEquiv

/-! ## `projection2x3`: the hexadic layer really is parity × ternary -/

/-- The hexadic universe splits as a parity bit times the ternary universe:
the Chinese remainder decomposition of `ℤ/6`, written out on the corpus's own
carriers. -/
def hexSplit : HexTruth ≃ ZMod 2 × ZMod 3 where
  toFun
    | .h0 => (0, 0) | .h1 => (1, 1) | .h2 => (0, 2)
    | .h3 => (1, 0) | .h4 => (0, 1) | .h5 => (1, 2)
  invFun := fun p =>
    if p = (0, 0) then .h0 else if p = (1, 1) then .h1 else if p = (0, 2) then .h2
    else if p = (1, 0) then .h3 else if p = (0, 1) then .h4 else .h5
  left_inv := by decide
  right_inv := by decide

/-- The splitting is additive: it carries `hexXor` to componentwise addition. -/
theorem hexSplit_xor (a b : HexTruth) :
    hexSplit (hexXor a b) = hexSplit a + hexSplit b := by
  cases a <;> cases b <;> decide

/-- The parity component of the splitting. -/
def hexParity : HexTruth → ZMod 2
  | .h0 => 0 | .h1 => 1 | .h2 => 0 | .h3 => 1 | .h4 => 0 | .h5 => 1

/-- The ternary component of the splitting, as a map onto the corpus's own
ternary universe rather than onto an anonymous `ZMod 3`. -/
def hexReduceTri : HexTruth → TriTruth
  | .h0 => .low | .h1 => .mid | .h2 => .high
  | .h3 => .low | .h4 => .mid | .h5 => .high

/-- The splitting is exactly (parity, `Base369` ternary layer). -/
theorem hexSplit_eq (h : HexTruth) : hexSplit h = (hexParity h, triIdx (hexReduceTri h)) := by
  cases h <;> decide

/-- Both components are homomorphisms, the ternary one onto the `Base369`
ternary XOR itself. -/
theorem hexParity_hom (a b : HexTruth) :
    hexParity (hexXor a b) = hexParity a + hexParity b := by
  cases a <;> cases b <;> decide

theorem hexReduceTri_hom (a b : HexTruth) :
    hexReduceTri (hexXor a b) = triXor (hexReduceTri a) (hexReduceTri b) := by
  cases a <;> cases b <;> decide

theorem hexReduceTri_surjective : Function.Surjective hexReduceTri := by decide

/-- The six hexadic beats are exactly the six parity/tone pairs. -/
theorem hexSplit_surjective : Function.Surjective hexSplit :=
  hexSplit.surjective

/-! ## The nonary layer is *not* two ternary layers -/

/-- In `ℤ/3 × ℤ/3` every element is killed by 3. -/
theorem three_smul_ternary_square (x : ZMod 3 × ZMod 3) : (3 : ℕ) • x = 0 := by
  obtain ⟨a, b⟩ := x
  revert a b
  decide

/-- In `ℤ/9` it is not. -/
theorem three_smul_nonary_ne : (3 : ℕ) • (1 : ZMod 9) ≠ 0 := by decide

/-- **No additive isomorphism** `ℤ/9 ≃+ ℤ/3 × ℤ/3`. -/
theorem zmod9_not_add_equiv_sq : IsEmpty (ZMod 9 ≃+ (ZMod 3 × ZMod 3)) := by
  constructor
  intro e
  have h : e ((3 : ℕ) • (1 : ZMod 9)) = (3 : ℕ) • e 1 := map_nsmul e 3 (1 : ZMod 9)
  rw [three_smul_ternary_square (e 1)] at h
  exact three_smul_nonary_ne (by simpa using e.injective (h.trans (map_zero e).symm))

/-- The corpus-level statement: **no bijection at all** carries the nonary XOR
to the componentwise ternary XOR.  So `NonaryTruth` and `TriTruth × TriTruth`
share a cardinality and a base-3 digit bijection, and nothing more. -/
theorem nonary_not_ternary_square :
    ¬ ∃ f : NonaryTruth ≃ TriTruth × TriTruth,
        ∀ a b, f (nonaryXor a b) = (triXor (f a).1 (f b).1, triXor (f a).2 (f b).2) := by
  rintro ⟨f, hf⟩
  -- The neutral element must go to the neutral pair: in `ℤ/3`, `p = 2p` forces `p = 0`.
  have hzero : ∀ p : TriTruth × TriTruth,
      p = (triXor p.1 p.1, triXor p.2 p.2) → p = (.low, .low) := by decide
  have h0 : f .n0 = (.low, .low) := by
    have h := hf .n0 .n0
    rw [show nonaryXor (NonaryTruth.n0) (NonaryTruth.n0) = NonaryTruth.n0 from by decide] at h
    exact hzero _ h
  -- but `.n3` is a triple sum, and every triple sum in `ℤ/3 × ℤ/3` is neutral.
  have h3 : f .n3 = (.low, .low) := by
    rw [show (NonaryTruth.n3) = nonaryXor .n1 (nonaryXor .n1 .n1) from by decide, hf, hf]
    have key : ∀ p : TriTruth × TriTruth,
        ((triXor p.1 (triXor p.1 p.1) : TriTruth), triXor p.2 (triXor p.2 p.2))
          = ((.low : TriTruth), (.low : TriTruth)) := by decide
    exact key (f .n1)
  exact absurd (f.injective (h3.trans h0.symm)) (by decide)

/-- The base-3 digit bijection *does* exist: this is exactly what makes the
junction level 3. -/
def nonaryDigits : NonaryTruth ≃ TriTruth × TriTruth where
  toFun
    | .n0 => (.low, .low)  | .n1 => (.low, .mid)  | .n2 => (.low, .high)
    | .n3 => (.mid, .low)  | .n4 => (.mid, .mid)  | .n5 => (.mid, .high)
    | .n6 => (.high, .low) | .n7 => (.high, .mid) | .n8 => (.high, .high)
  invFun
    | (.low, .low) => .n0  | (.low, .mid) => .n1  | (.low, .high) => .n2
    | (.mid, .low) => .n3  | (.mid, .mid) => .n4  | (.mid, .high) => .n5
    | (.high, .low) => .n6 | (.high, .mid) => .n7 | (.high, .high) => .n8
  left_inv := by decide
  right_inv := by decide

/-- …and it is *not* a homomorphism, as it cannot be: carrying `.n2 = 2` and
`.n1 = 1` to digit pairs and adding componentwise loses the carry. -/
theorem nonaryDigits_not_hom :
    ∃ a b : NonaryTruth, nonaryDigits (nonaryXor a b) ≠
      (triXor (nonaryDigits a).1 (nonaryDigits b).1,
       triXor (nonaryDigits a).2 (nonaryDigits b).2) :=
  ⟨.n2, .n1, by decide⟩

/-! ## What the 3–9 relation actually is: a non-split extension -/

/-- The ternary layer sits inside the nonary layer as the order-3 subgroup
(multiplication by 3). -/
def triInNonary : TriTruth → NonaryTruth
  | .low => .n0 | .mid => .n3 | .high => .n6

/-- The nonary layer reduces onto the ternary layer. -/
def nonaryReduce : NonaryTruth → TriTruth
  | .n0 => .low  | .n1 => .mid  | .n2 => .high
  | .n3 => .low  | .n4 => .mid  | .n5 => .high
  | .n6 => .low  | .n7 => .mid  | .n8 => .high

theorem triInNonary_hom (a b : TriTruth) :
    triInNonary (triXor a b) = nonaryXor (triInNonary a) (triInNonary b) := by
  cases a <;> cases b <;> decide

theorem triInNonary_injective : Function.Injective triInNonary := by decide

theorem nonaryReduce_hom (a b : NonaryTruth) :
    nonaryReduce (nonaryXor a b) = triXor (nonaryReduce a) (nonaryReduce b) := by
  cases a <;> cases b <;> decide

theorem nonaryReduce_surjective : Function.Surjective nonaryReduce := by decide

/-- Exactness at the middle: the kernel of the reduction is exactly the image of
the embedding. -/
theorem nonary_extension (n : NonaryTruth) :
    nonaryReduce n = .low ↔ ∃ t, triInNonary t = n := by
  revert n; decide

/-- The extension does not split as a direct product — this is
`nonary_not_ternary_square` again, and it is the exact sense in which "9 = 3 × 3"
fails in `Base369`. -/
theorem nonary_extension_nonsplit :
    ¬ ∃ f : NonaryTruth ≃ TriTruth × TriTruth,
        ∀ a b, f (nonaryXor a b) = (triXor (f a).1 (f b).1, triXor (f a).2 (f b).2) :=
  nonary_not_ternary_square

/-! ## Absence: the loom's `projection2x9` has no carrier -/

/-- `DialecticalJourneyLoom.LoomProjectionTag` lists `projection2x9`, but
`Base369` defines universes of size 3, 6 and 9 only, so there is nothing of size
18 for that tag to project.  Recorded here as the exact cardinality statement,
so that the absence is part of the checked map rather than a remark. -/
theorem base369_carrier_cards :
    Fintype.card TriTruth = 3 ∧ Fintype.card HexTruth = 6 ∧
      Fintype.card NonaryTruth = 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end Integration.Base369Group
