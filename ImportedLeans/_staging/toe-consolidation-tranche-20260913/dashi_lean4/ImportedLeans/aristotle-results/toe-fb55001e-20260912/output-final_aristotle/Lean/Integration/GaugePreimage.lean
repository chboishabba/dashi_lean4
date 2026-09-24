import Integration.GaugeReduction

/-!
# Composing gauge reductions: the preimage subgroup

`Integration.Gauge.compGauge_redundant_iff` says that after composing two gauge
reductions the symmetries invisible downstairs are exactly those `g` whose image
in the middle symmetry lies in the second gauge subgroup — the *set*
`quot⁻¹(K)`.  That is a characterisation, not yet an algebraic composition law:
the composite was still presented as a gauge reduction whose declared gauge
group was the *first* one, `H`, which is in general too small.

This file promotes that set to actual subgroup data and closes the composition
law.

* `PreimageCarrier A Bq = {g : G // ∃ k, A.quot g = Bq.incl k}` — the preimage of
  the second gauge subgroup, with its inherited monoid structure
  (`preimageMonoid`): it contains `1` and is closed under multiplication
  precisely because `quot` is multiplicative and `incl` is a monoid map.
* `inclFirst` — the first gauge subgroup sits inside it, so composing only ever
  makes more symmetry redundant.
* `compGaugeQuotient` — the composite symmetry datum
  `PreimageCarrier → G ↠ P`.
* `compGaugeQuotient_exact` — **the composition law**: if the second stage is
  exact then so is the composite, i.e. `P` is exactly `G` modulo the preimage
  subgroup.  In the usual notation this is `(G/H)/K ≅ G/quot⁻¹(K)`.
* `preimage_inv_mem`, `preimage_normal` — in the group case the preimage is
  closed under inverses, and is normal as soon as the second gauge subgroup is.
* `compGaugeExact` — the composite *reduction*, now carrying the honest gauge
  subgroup, and `compGaugeExact_redundant_iff` — for it, `redundant_iff_gauge`
  applies: the symmetries invisible to the composite coarse layer are exactly
  the elements of the preimage subgroup, nothing more and nothing less.

Everything is stated for monoid actions; the two inverse-related results assume
groups, which is where they have content.
-/

namespace Integration.Gauge

variable {G H Q K P Rich Mid Coarse : Type} [Monoid G] [Monoid H] [Monoid Q] [Monoid K]
  [Monoid P]

/-! ## The preimage subgroup -/

/-- The carrier of the composite gauge subgroup: the symmetries whose image in
the middle symmetry is a second-stage gauge element. -/
def PreimageCarrier (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P) : Type :=
  {g : G // ∃ k, A.quot g = Bq.incl k}

namespace PreimageCarrier

variable {A : GaugeQuotient G H Q} {Bq : GaugeQuotient Q K P}

/-- Its elements are symmetries. -/
def val (x : PreimageCarrier A Bq) : G := x.1

@[ext] theorem ext {x y : PreimageCarrier A Bq} (h : x.val = y.val) : x = y := Subtype.ext h

/-- The preimage of a submonoid is a submonoid. -/
instance preimageMonoid (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P) :
    Monoid (PreimageCarrier A Bq) where
  mul x y := ⟨x.1 * y.1, by
    obtain ⟨k, hk⟩ := x.2
    obtain ⟨l, hl⟩ := y.2
    exact ⟨k * l, by rw [A.quot_mul, hk, hl, Bq.incl_mul]⟩⟩
  one := ⟨1, ⟨1, by rw [A.quot_one, Bq.incl_one]⟩⟩
  mul_assoc x y z := Subtype.ext (mul_assoc x.1 y.1 z.1)
  one_mul x := Subtype.ext (one_mul x.1)
  mul_one x := Subtype.ext (mul_one x.1)

@[simp] theorem val_one : (1 : PreimageCarrier A Bq).val = 1 := rfl

@[simp] theorem val_mul (x y : PreimageCarrier A Bq) :
    (x * y).val = x.val * y.val := rfl

end PreimageCarrier

/-- The first gauge subgroup is contained in the composite one. -/
def inclFirst (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P) (h : H) :
    PreimageCarrier A Bq :=
  ⟨A.incl h, ⟨1, by rw [A.quot_incl, Bq.incl_one]⟩⟩

@[simp] theorem inclFirst_val (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P) (h : H) :
    (inclFirst A Bq h).val = A.incl h := rfl

/-! ## The composite symmetry datum -/

/-- The composite gauge quotient `quot⁻¹(K) → G ↠ P`. -/
def compGaugeQuotient (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P) :
    GaugeQuotient G (PreimageCarrier A Bq) P where
  incl := Subtype.val
  incl_one := rfl
  incl_mul := fun _ _ => rfl
  quot := fun g => Bq.quot (A.quot g)
  quot_one := by rw [A.quot_one, Bq.quot_one]
  quot_mul := fun a b => by rw [A.quot_mul, Bq.quot_mul]
  quot_surjective := Bq.quot_surjective.comp A.quot_surjective
  quot_incl := fun x => by
    obtain ⟨k, hk⟩ := x.2
    show Bq.quot (A.quot x.1) = 1
    rw [hk, Bq.quot_incl]

@[simp] theorem compGaugeQuotient_quot (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P)
    (g : G) : (compGaugeQuotient A Bq).quot g = Bq.quot (A.quot g) := rfl

/-- **The composition law for gauge redundancy.**  If the second stage is exact,
so is the composite: the effective symmetry `P` is exactly `G` modulo the
preimage subgroup `quot⁻¹(K)`.  This is `(G/H)/K ≅ G/quot⁻¹(K)` in the form the
library uses. -/
theorem compGaugeQuotient_exact (A : GaugeQuotient G H Q) (Bq : GaugeQuotient Q K P)
    (hex : Bq.Exact) : (compGaugeQuotient A Bq).Exact := by
  intro g hg
  obtain ⟨k, hk⟩ := hex (A.quot g) hg
  exact ⟨⟨g, ⟨k, hk⟩⟩, rfl⟩

/-! ## The group case: inverses and normality -/

section Groups

-- Group-level statements use their own variables so that the group structure is
-- the only multiplicative structure on the carriers.
variable {G' H' Q' K' P' : Type} [Group G'] [Monoid H'] [Group Q'] [Monoid K'] [Monoid P']

/-- In a group, a multiplicative unital map sends inverses to inverses. -/
theorem quot_inv (A : GaugeQuotient G' H' Q') (g : G') : A.quot g⁻¹ = (A.quot g)⁻¹ := by
  have h : A.quot g * A.quot g⁻¹ = 1 := by
    rw [← A.quot_mul, mul_inv_cancel, A.quot_one]
  exact Eq.symm (DivisionMonoid.inv_eq_of_mul _ _ h)

/-- The preimage subgroup is closed under inverses. -/
theorem preimage_inv_mem (A : GaugeQuotient G' H' Q') (Bq : GaugeQuotient Q' K' P')
    (hKinv : ∀ k, ∃ k', (Bq.incl k)⁻¹ = Bq.incl k') {g : G'} (hg : ∃ k, A.quot g = Bq.incl k) :
    ∃ k, A.quot g⁻¹ = Bq.incl k := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨k', hk'⟩ := hKinv k
  exact ⟨k', by rw [quot_inv, hk, hk']⟩

/-- **Normality is inherited.**  If the second gauge subgroup is normal in the
middle symmetry, the preimage subgroup is normal in the full symmetry. -/
theorem preimage_normal (A : GaugeQuotient G' H' Q') (Bq : GaugeQuotient Q' K' P')
    (hKnormal : ∀ (q : Q') (k : K'), ∃ k', q * Bq.incl k * q⁻¹ = Bq.incl k')
    (g : G') {x : G'} (hx : ∃ k, A.quot x = Bq.incl k) :
    ∃ k, A.quot (g * x * g⁻¹) = Bq.incl k := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨k', hk'⟩ := hKnormal (A.quot g) k
  refine ⟨k', ?_⟩
  rw [A.quot_mul, A.quot_mul, hk, quot_inv, hk']

end Groups

/-! ## The composite reduction with its honest gauge subgroup -/

/-- The composite of two gauge reductions, presented with the *correct* gauge
subgroup: the preimage of the second one rather than the first one. -/
def compGaugeExact (A : GaugeReduction G H Q Rich Mid) (B : GaugeReduction Q K P Mid Coarse)
    (hmid : ∀ q y, B.actRich q y = A.actCoarse q y) :
    GaugeReduction G (PreimageCarrier A.gq B.gq) P Rich Coarse where
  gq := compGaugeQuotient A.gq B.gq
  actRich := A.actRich
  rich_one := A.rich_one
  rich_mul := A.rich_mul
  actCoarse := B.actCoarse
  coarse_one := B.coarse_one
  coarse_mul := B.coarse_mul
  red := fun x => B.red (A.red x)
  red_surjective := B.red_surjective.comp A.red_surjective
  square := fun g x => by
    show B.red (A.red (A.actRich g x)) = B.actCoarse (B.gq.quot (A.gq.quot g)) (B.red (A.red x))
    rw [A.square, ← hmid, B.square]

@[simp] theorem compGaugeExact_red (A : GaugeReduction G H Q Rich Mid)
    (B : GaugeReduction Q K P Mid Coarse) (hmid : ∀ q y, B.actRich q y = A.actCoarse q y)
    (x : Rich) : (compGaugeExact A B hmid).red x = B.red (A.red x) := rfl

/-- **The composite removes exactly the preimage subgroup.**  With the honest
gauge subgroup in place, the general theorem `redundant_iff_gauge` applies to the
composite: a symmetry is invisible to the composite coarse layer if and only if
it is an element of `quot⁻¹(K)`. -/
theorem compGaugeExact_redundant_iff (A : GaugeReduction G H Q Rich Mid)
    (B : GaugeReduction Q K P Mid Coarse) (hmid : ∀ q y, B.actRich q y = A.actCoarse q y)
    (hex : B.gq.Exact) (hfaith : B.CoarseFaithful) (g : G) :
    (∀ x, (compGaugeExact A B hmid).red ((compGaugeExact A B hmid).actRich g x)
        = (compGaugeExact A B hmid).red x)
      ↔ ∃ h : PreimageCarrier A.gq B.gq, g = h.val :=
  GaugeReduction.redundant_iff_gauge (compGaugeExact A B hmid)
    (compGaugeQuotient_exact A.gq B.gq hex) hfaith g

/-- The composite is effective exactly when the second stage is: what survives
the two reductions is the second stage's effective symmetry. -/
theorem compGaugeExact_effective_iff (A : GaugeReduction G H Q Rich Mid)
    (B : GaugeReduction Q K P Mid Coarse) (hmid : ∀ q y, B.actRich q y = A.actCoarse q y) :
    (compGaugeExact A B hmid).Effective ↔ B.Effective := Iff.rfl

end Integration.Gauge
