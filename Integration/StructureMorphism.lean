import Integration.ApproximateIntertwiner
import Integration.GaugeReduction

/-!
# One owner for the commuting square

Four lanes of this corpus independently arrived at the same object:

* a **representation/kernel compatibility**: a one-step square between a machine
  step and its representation, from which trajectory, fixed-point and finite
  reachability transport are then inherited;
* an **intertwiner** (`Integration.ApproximateIntertwiner`), exact or certified
  approximate, with additive error under composition;
* a **quotient soundness** witness, which is the refusal to transport a property
  across an observer quotient until a commuting/soundness certificate is
  supplied;
* a **gauge reduction** (`Integration.Gauge`), where the square is indexed by a
  group element and the vertical maps are the same reduction.

This file makes the square the owner and the four lanes its tiers.  The exact
tier is `Integration.ApproximateIntertwiner.IsIntertwiner`, re-exported here as
`Exact`, so there is exactly one definition of "the square commutes" in the
tree.

```
Exact        q (f a) = g (q a)
Approx ε     dist (q (f a)) (g (q a)) ≤ ε
Sound P      q s = q t → P s → P t
Dynamic      q (f^[n] a) = g^[n] (q a),  reachability transports
Gauge        q (act γ x) = actB (hom γ) (q x)
```

Contents.

* `Exact`, `Tier`, `Tier.Holds` — the square and its three verification tiers
  (exact, certified approximate, unverified), with `tier_exact_le_approx`
  placing the exact tier inside the approximate one and
  `tier_unverified_vacuous` recording that the unverified tier really is
  vacuous, so filing a square there is an honest statement of ignorance;
* `exact_iterate`, `exact_fixed`, `Reaches`, `exact_reaches` — **everything the
  representation-compatibility lane inherits from one step**: `n`-step
  transport, fixed points map to fixed points, reachability maps to
  reachability;
* `reaches_not_reflected` — and the honest converse failure: the image of a
  reachability need not lift, so an exact square transports forwards only;
* `Sound`, `sound_iff_factors`, `sound_of_factors`, `not_sound_of_collision` —
  the proof-search tier: a property transports across an observer quotient
  exactly when it factors through the quotient, and without that witness it can
  fail (explicit two-state counterexample);
* `Gauge`, `Gauge.toExact`, `gauge_of_gaugeReduction`,
  `gauge_of_equivariantQuotient` — the group-indexed tier and the two existing
  lanes as instances of it;
* `approx_of_gauge` — a gauge square is in particular a certified approximate
  square at error zero, which is how the group-indexed lane inherits the
  additive-error composition calculus;
* `structure_morphism_unification` — one checked record asserting that all four
  lanes are instances of the same predicate.

No new mathematics is claimed here: the content is that the four lanes are the
same predicate, and that the transport theorems belong to the predicate rather
than to any one lane.
-/

namespace Integration.StructureMorphism

open Integration.ApproximateIntertwiner
open Integration.Gauge
open Integration.SymmetryReduction

variable {A B C : Type*}

/-! ## The square, and the tier it is filed at -/

/-- **The owner.**  `Exact q f g` says the square

```
   A --f--> A
   |        |
   q        q
   v        v
   B --g--> B
```

commutes.  It is definitionally `IsIntertwiner`, so no second notion of
commuting square exists in the tree. -/
abbrev Exact (q : A → B) (f : A → A) (g : B → B) : Prop := IsIntertwiner q f g

theorem exact_def {q : A → B} {f : A → A} {g : B → B} :
    Exact q f g ↔ ∀ a, q (f a) = g (q a) := Iff.rfl

/-- The three tiers a claimed square may be filed at. -/
inductive Tier (ε : ℝ) : Type
  /-- The square commutes on the nose. -/
  | exact : Tier ε
  /-- The square commutes to within the stated error. -/
  | approx : Tier ε
  /-- No square is asserted. -/
  | unverified : Tier ε
  deriving DecidableEq, Repr

/-- What each tier asserts. -/
def Tier.Holds [PseudoMetricSpace B] {ε : ℝ} : Tier ε → (A → B) → (A → A) → (B → B) → Prop
  | .exact, q, f, g => Exact q f g
  | .approx, q, f, g => IsApproxIntertwiner q f g ε
  | .unverified, _, _, _ => True

/-- The exact tier is contained in the approximate tier at every nonnegative
error. -/
theorem tier_exact_le_approx [PseudoMetricSpace B] {ε : ℝ} (hε : 0 ≤ ε) (q : A → B) (f : A → A) (g : B → B)
    (h : Tier.Holds (ε := ε) .exact q f g) : Tier.Holds (ε := ε) .approx q f g :=
  approx_of_exact_le hε h

/-- And the unverified tier is genuinely vacuous: it holds of a square that does
not commute, so it carries no information. -/
theorem tier_unverified_vacuous :
    Tier.Holds (ε := (0 : ℝ)) .unverified (fun b : Bool => if b then (1 : ℝ) else 0) not id ∧
      ¬ Tier.Holds (ε := (0 : ℝ)) .exact (fun b : Bool => if b then (1 : ℝ) else 0) not id := by
  refine ⟨trivial, ?_⟩
  intro h
  simpa using h true

/-! ## What one exact square buys: the dynamic tier -/

variable {q : A → B} {f : A → A} {g : B → B}

/-- **`n`-step transport.**  A one-step square gives every finite trajectory. -/
theorem exact_iterate (h : Exact q f g) : ∀ (n : ℕ) (a : A), q (f^[n] a) = g^[n] (q a) := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (f a), h a]

/-- **Fixed points transport.** -/
theorem exact_fixed (h : Exact q f g) {a : A} (ha : f a = a) : g (q a) = q a := by
  rw [← h a, ha]

/-- `b` is reachable from `a` in finitely many steps. -/
def Reaches (f : A → A) (a b : A) : Prop := ∃ n : ℕ, f^[n] a = b

theorem reaches_refl (f : A → A) (a : A) : Reaches f a a := ⟨0, rfl⟩

theorem reaches_trans {f : A → A} {a b c : A} (hab : Reaches f a b) (hbc : Reaches f b c) :
    Reaches f a c := by
  obtain ⟨m, rfl⟩ := hab
  obtain ⟨n, rfl⟩ := hbc
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

/-- **Finite reachability transports.** -/
theorem exact_reaches (h : Exact q f g) {a b : A} (hab : Reaches f a b) :
    Reaches g (q a) (q b) := by
  obtain ⟨n, rfl⟩ := hab
  exact ⟨n, (exact_iterate h n a).symm⟩

/-- **The honest direction gate.**  Transport runs forwards only: there is an
exact square, and a downstream reachability, whose lift fails.  So "the reduced
system reaches this" is not evidence that the rich system does. -/
theorem reaches_not_reflected :
    ∃ (q : Bool → Unit) (f : Bool → Bool) (g : Unit → Unit),
      Exact q f g ∧ Reaches g (q false) (q true) ∧ ¬ Reaches f false true := by
  refine ⟨fun _ => (), id, id, fun _ => rfl, ⟨0, rfl⟩, ?_⟩
  rintro ⟨n, hn⟩
  simp at hn

/-! ## The proof-search tier: transport of a property across a quotient -/

/-- A property is **sound for the observer** `q` when states with the same
observation agree on it.  This is the `QuotientSound` witness: without it, no
property is transported across the quotient. -/
def Sound (q : A → B) (P : A → Prop) : Prop := ∀ s t, q s = q t → P s → P t

/-- A property pulled back along the observer is automatically sound. -/
theorem sound_of_factors (q : A → B) (P' : B → Prop) : Sound q (fun a => P' (q a)) := by
  intro s t hst hs
  rwa [← hst]

/-- **And conversely.**  Soundness is exactly factorisation through the
observation: this is the precise content of "structure transports through a
quotient only under a commuting/soundness certificate". -/
theorem sound_iff_factors (q : A → B) (P : A → Prop) :
    Sound q P ↔ ∃ P' : B → Prop, ∀ a, P a ↔ P' (q a) := by
  classical
  constructor
  · intro h
    refine ⟨fun b => ∃ a, q a = b ∧ P a, fun a => ⟨fun ha => ⟨a, rfl, ha⟩, ?_⟩⟩
    rintro ⟨a', ha', hP⟩
    exact h a' a ha' hP
  · rintro ⟨P', hP⟩ s t hst hs
    exact (hP t).mpr (by rw [← hst]; exact (hP s).mp hs)

/-- Soundness transports a proved property along the quotient, which is the
statement the proof-search lane wants:
`s ∼ t ∧ Proved s → Proved t`. -/
theorem sound_transport {q : A → B} {P : A → Prop} (h : Sound q P) {s t : A}
    (hst : q s = q t) (hs : P s) : P t := h s t hst hs

/-- **Without the witness the transport is false.**  Two states with the same
observation, one satisfying the property and one not. -/
theorem not_sound_of_collision :
    ∃ (q : Bool → Unit) (P : Bool → Prop), ¬ Sound q P := by
  refine ⟨fun _ => (), fun b => b = true, ?_⟩
  intro h
  simpa using h true false rfl rfl

/-- A dynamic property phrased **downstream** is always sound, and an upstream
reachability into an observed target implies it.  This is the honest version of
"the reachability property transports": the transported statement is about the
observed trajectory, not about the rich one. -/
theorem sound_reaches_image (q : A → B) (g : B → B) (S : B → Prop) :
    Sound q (fun a => ∃ y, Reaches g (q a) y ∧ S y) :=
  sound_of_factors q (fun b => ∃ y, Reaches g b y ∧ S y)

theorem reaches_image_of_reaches (h : Exact q f g) {S : B → Prop} {a b : A}
    (hab : Reaches f a b) (hS : S (q b)) : ∃ y, Reaches g (q a) y ∧ S y :=
  ⟨q b, exact_reaches h hab, hS⟩

/-! ## The group-indexed tier -/

/-- A **gauge morphism**: the square, indexed by a symmetry element, with the
symmetry itself mapped along `hom`. -/
def Gauge {G Q : Type*} (hom : G → Q) (act : G → A → A) (actB : Q → B → B) (q : A → B) : Prop :=
  ∀ γ x, q (act γ x) = actB (hom γ) (q x)

/-- Each symmetry element of a gauge morphism gives an exact square. -/
theorem Gauge.toExact {G Q : Type*} {hom : G → Q} {act : G → A → A} {actB : Q → B → B}
    {q : A → B} (h : Gauge hom act actB q) (γ : G) : Exact q (act γ) (actB (hom γ)) :=
  fun x => h γ x

/-- The gauge-reduction lane is an instance. -/
theorem gauge_of_gaugeReduction {G H Q Rich Coarse : Type} [Monoid G] [Monoid H] [Monoid Q]
    (R : GaugeReduction G H Q Rich Coarse) :
    Gauge R.gq.quot R.actRich R.actCoarse R.red := R.square

/-- The equivariant-quotient lane is an instance (with the identity on
symmetries). -/
theorem gauge_of_equivariantQuotient {G Rich Coarse : Type} [Monoid G]
    (E : EquivariantQuotient G Rich Coarse) :
    Gauge id E.actRich E.actCoarse E.proj := E.square

/-- Hence the group-indexed lane inherits the approximate calculus for free: a
gauge square is a certified approximate square at error zero. -/
theorem approx_of_gauge [PseudoMetricSpace B] {G Q : Type*} {hom : G → Q} {act : G → A → A} {actB : Q → B → B}
    {q : A → B} (h : Gauge hom act actB q) (γ : G) :
    IsApproxIntertwiner q (act γ) (actB (hom γ)) 0 :=
  approx_of_exact (h.toExact γ)

/-- And the trajectory transport: acting by one symmetry `n` times commutes with
the reduction. -/
theorem gauge_iterate {G Q : Type*} {hom : G → Q} {act : G → A → A} {actB : Q → B → B}
    {q : A → B} (h : Gauge hom act actB q) (γ : G) (n : ℕ) (x : A) :
    q ((act γ)^[n] x) = (actB (hom γ))^[n] (q x) :=
  exact_iterate (h.toExact γ) n x

/-! ## The unification statement -/

/-- **The four lanes are one predicate.**  For a gauge reduction `R`, a metric
target, and any property pulled back along the reduction:

* the group-indexed square holds (`Gauge`),
* each of its instances is an exact square (`Exact`),
* each of those is a certified approximate square at error zero,
* trajectories transport,
* and the pulled-back property is `Sound` for the reduction.

So `RepresentationKernelCompatibility`, `Intertwiner`, `QuotientSound` and
`GaugeReduction` are wrappers around one owner, not four cores. -/
theorem structure_morphism_unification {G H Q Rich : Type} [Monoid G] [Monoid H] [Monoid Q]
    {Coarse : Type} [PseudoMetricSpace Coarse]
    (R : GaugeReduction G H Q Rich Coarse) (P' : Coarse → Prop) (γ : G) :
    Gauge R.gq.quot R.actRich R.actCoarse R.red ∧
      Exact R.red (R.actRich γ) (R.actCoarse (R.gq.quot γ)) ∧
      IsApproxIntertwiner R.red (R.actRich γ) (R.actCoarse (R.gq.quot γ)) 0 ∧
      (∀ (n : ℕ) (x : Rich), R.red ((R.actRich γ)^[n] x)
        = (R.actCoarse (R.gq.quot γ))^[n] (R.red x)) ∧
      Sound R.red (fun x => P' (R.red x)) :=
  ⟨R.square, (gauge_of_gaugeReduction R).toExact γ,
    approx_of_gauge (gauge_of_gaugeReduction R) γ,
    gauge_iterate (gauge_of_gaugeReduction R) γ,
    sound_of_factors R.red P'⟩

end Integration.StructureMorphism
