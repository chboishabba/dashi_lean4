import Integration.Kernel.EvidenceDependence

/-!
# Consumer-indexed adequacy: evidence enough for one consumer is not enough for another

`Agda/DASHI/Biology/DrosophilaConsumerIndexedEvidencePromotionExact.agda` (in the
6 September tranche archive shipped with this project) supplies the index the
Lean promotion layer was missing.  `Integration.PromotionEvidence` already
separates "the transition shape is licensed" from "this row inhabits the
receipt"; what it has no coordinate for is *which consumer* the evidence is
adequate for.  The Agda module introduces `EvidenceConsumer`, a required-channel
policy, consumer-carrying bundles, and a `CrossConsumerTransfer` record.

**What that Agda module contains, and what it does not.**  `required` and
`optional` are genuine `EvidenceConsumer → List EvidenceChannel` fields, but
`allRequiredPresent`, `provenanceAdequate`, `promotionAdmissible` and
`transferAdmissible` are `Bool` fields (the first three with `≡ true`
obligations discharged by the record's builder), not values computed from the
listed channels.  So the *indexed architecture* is what crosses over; none of
those flags is transported as evidence.  Here adequacy is **defined** from the
channels and the policy, and the transfer rule is proved rather than declared.

## What is proved

* `AdequateFor E c := required c ⊆ E` — adequacy is computed, not asserted;
  `adequateFor_mono` and `adequateFor_required` are its basic shape.
* **`adequacy_is_consumer_relative`** — a bundle adequate for one consumer and
  inadequate for another, so `AdequateFor` genuinely depends on both arguments.
* **`bridge_iff_transfers`** — the firewall theorem, in its sharp form: the
  evidence adequate for `c` is adequate for `d` *for every bundle* **iff** a
  bridge `required d ⊆ required c` exists.  So cross-consumer transfer is never
  free: it is exactly the existence of the bridge, and
  `no_silent_transfer` exhibits a pair with no bridge.
* `Bridge` is reflexive and transitive (`bridge_refl`, `bridge_trans`), so
  consumers with bridges form a preorder along which receipts flow.
* **`Receipt`** — a promotion receipt for a consumer is a *structure carrying a
  proof* of `AdequateFor`, not a Boolean field.  `Receipt.transfer` moves one
  along a bridge, and `no_receipt_without_adequacy` /
  `receipt_does_not_transfer_without_bridge` are the two negatives: a receipt
  cannot be built without adequacy, and a receipt for one consumer does not
  produce one for another.
* **`adequacy_does_not_descend_through_bundle`** — the kernel statement: the
  adequacy verdict is not a function of the bundle alone, via
  `Integration.Kernel.Quotient.not_descendsThrough_of_collision`.
* `independence_required_is_a_separate_gate` — the composite gate, joining this
  file's channel adequacy to `Integration.Kernel.EvidenceDependence`: a bundle
  can hold every required channel and still fail an independence requirement,
  so the two coordinates are not the same test.

**Claim boundary.**  `Consumer` and `Channel` are arbitrary types and the policy
is an arbitrary function; nothing is claimed about any experimental modality,
benchmark or organism.
-/

namespace Integration.Kernel.ConsumerPromotion

open Integration.Kernel.Quotient

universe u v

variable {Consumer : Type u} {Channel : Type v}

/-! ## §1 Required channels and consumer-relative adequacy -/

/-- What each consumer requires.  Only the *required* channels matter for
adequacy; optional ones are, by definition, not part of the gate. -/
structure Policy (Consumer : Type u) (Channel : Type v) where
  /-- The channels a consumer's promotion requires. -/
  required : Consumer → Finset Channel

/-- The channels a bundle actually holds. -/
abbrev Bundle (Channel : Type v) : Type v := Finset Channel

variable (Pol : Policy Consumer Channel)

/-- **Adequacy is consumer-indexed and computed**: the bundle holds everything
this consumer requires. -/
def AdequateFor (E : Bundle Channel) (c : Consumer) : Prop := Pol.required c ⊆ E

instance [DecidableEq Channel] (Pol : Policy Consumer Channel) (E : Bundle Channel)
    (c : Consumer) : Decidable (AdequateFor Pol E c) :=
  inferInstanceAs (Decidable (_ ⊆ _))

variable {Pol}

theorem adequateFor_iff {E : Bundle Channel} {c : Consumer} :
    AdequateFor Pol E c ↔ Pol.required c ⊆ E := Iff.rfl

/-- Adding channels never destroys adequacy. -/
theorem adequateFor_mono {E F : Bundle Channel} {c : Consumer} (h : E ⊆ F)
    (hE : AdequateFor Pol E c) : AdequateFor Pol F c := hE.trans h

/-- The requirement set is the least adequate bundle. -/
theorem adequateFor_required (c : Consumer) : AdequateFor Pol (Pol.required c) c :=
  subset_rfl

/-! ## §2 Cross-consumer transfer needs a bridge -/

/-- A **bridge** from `c` to `d`: everything `d` requires is already required by
`c`.  This is the transfer receipt, and unlike the Agda `transferAdmissible`
field it is a proposition about the policy, not a Boolean. -/
def Bridge (Pol : Policy Consumer Channel) (c d : Consumer) : Prop :=
  Pol.required d ⊆ Pol.required c

instance [DecidableEq Channel] (Pol : Policy Consumer Channel) (c d : Consumer) :
    Decidable (Bridge Pol c d) := inferInstanceAs (Decidable (_ ⊆ _))

theorem bridge_refl (c : Consumer) : Bridge Pol c c := subset_rfl

theorem bridge_trans {c d e : Consumer} (h₁ : Bridge Pol c d) (h₂ : Bridge Pol d e) :
    Bridge Pol c e := h₂.trans h₁

/-- Along a bridge, adequacy transfers. -/
theorem adequate_transfer {E : Bundle Channel} {c d : Consumer}
    (hE : AdequateFor Pol E c) (h : Bridge Pol c d) : AdequateFor Pol E d := h.trans hE

/-- **The firewall, sharply.**  Adequacy for `c` implies adequacy for `d` on
*every* bundle exactly when a bridge exists.  So there is no evidence-level
route around a missing bridge: if transfer holds for all bundles the bridge is
already there, and if it does not, `Pol.required c` itself is the
counterexample. -/
theorem bridge_iff_transfers (c d : Consumer) :
    Bridge Pol c d ↔ ∀ E : Bundle Channel, AdequateFor Pol E c → AdequateFor Pol E d := by
  constructor
  · intro h E hE
    exact adequate_transfer hE h
  · intro h
    exact h (Pol.required c) (adequateFor_required c)

/-! ## §3 The separations -/

/-- Two consumers requiring different single channels. -/
def twoConsumerPolicy : Policy Bool ℕ := ⟨fun b => if b then {0} else {1}⟩

/-- **Adequacy is consumer-relative.**  One bundle, two consumers, one verdict
each way. -/
theorem adequacy_is_consumer_relative :
    AdequateFor twoConsumerPolicy {0} true ∧ ¬ AdequateFor twoConsumerPolicy {0} false := by
  constructor <;> decide

/-- **No silent transfer.**  There is no bridge between those two consumers, and
`bridge_iff_transfers` therefore forbids moving the receipt across. -/
theorem no_silent_transfer : ¬ Bridge twoConsumerPolicy true false := by decide

/-- **The adequacy verdict is not a function of the bundle.**  The kernel form of
consumer-indexing: forgetting which consumer asked destroys the answer. -/
theorem adequacy_does_not_descend_through_bundle :
    ¬ DescendsThrough
        (fun p : Bundle ℕ × Bool => decide (AdequateFor twoConsumerPolicy p.1 p.2))
        (fun p : Bundle ℕ × Bool => p.1) :=
  not_descendsThrough_of_collision (x := ({0}, true)) (y := ({0}, false)) rfl (by decide)

/-! ## §4 Receipts carry proofs, not flags -/

/-- A consumer-indexed promotion receipt.  The adequacy field is a **proof**:
the structure cannot be built by asserting a Boolean. -/
structure Receipt (Pol : Policy Consumer Channel) (c : Consumer) : Type v where
  /-- The evidence bundle offered. -/
  bundle : Bundle Channel
  /-- Proof that the bundle meets this consumer's requirements. -/
  adequate : AdequateFor Pol bundle c

/-- A receipt is exactly an adequate bundle: no receipt exists for a consumer no
bundle satisfies, and none can be manufactured from a status flag. -/
theorem no_receipt_without_adequacy {c : Consumer} (r : Receipt Pol c) :
    AdequateFor Pol r.bundle c := r.adequate

/-- Receipts flow along bridges, keeping the same evidence. -/
def Receipt.transfer {c d : Consumer} (r : Receipt Pol c) (h : Bridge Pol c d) :
    Receipt Pol d := ⟨r.bundle, adequate_transfer r.adequate h⟩

@[simp] theorem Receipt.transfer_bundle {c d : Consumer} (r : Receipt Pol c)
    (h : Bridge Pol c d) : (r.transfer h).bundle = r.bundle := rfl

/-- **A receipt for one consumer is not a receipt for another.**  The evidence
that satisfies the first consumer is exhibited, and it provably fails the
second. -/
theorem receipt_does_not_transfer_without_bridge :
    ∃ r : Receipt twoConsumerPolicy true,
      ¬ AdequateFor twoConsumerPolicy r.bundle false :=
  ⟨⟨{0}, by decide⟩, by decide⟩

/-! ## §5 Channel adequacy is not provenance adequacy

The Agda bundle carries `allRequiredPresent` and `provenanceAdequate` as two
separate flags.  They are indeed two separate gates: holding every required
channel says nothing about whether the artefacts behind those channels have
disjoint provenance. -/

/-- A composite gate: the required channels, **and** an independence requirement
on the evidence units behind them. -/
def AdequateAndIndependent {E' R : Type} [DecidableEq R]
    (Pol : Policy Consumer Channel) (P : EvidenceDependence.Provenance E' R)
    (E : Bundle Channel) (c : Consumer) (units : E' × E') : Prop :=
  AdequateFor Pol E c ∧ EvidenceDependence.Independent P units.1 units.2

/-- **The two gates are independent of each other.**  A bundle can hold every
required channel while the two evidence units behind it share a provenance root,
so channel adequacy never certifies independence. -/
theorem independence_required_is_a_separate_gate :
    ∃ P : EvidenceDependence.Provenance (Fin 2) ℕ,
      AdequateFor twoConsumerPolicy {0} true ∧
        ¬ AdequateAndIndependent twoConsumerPolicy P {0} true (0, 1) := by
  refine ⟨⟨fun _ => {0}⟩, by decide, ?_⟩
  rintro ⟨-, hind⟩
  exact EvidenceDependence.shared_root_blocks_independent_replication
    ⟨0, Finset.mem_singleton_self 0, Finset.mem_singleton_self 0⟩ hind

end Integration.Kernel.ConsumerPromotion
