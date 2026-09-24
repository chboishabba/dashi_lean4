import Integration.StructuredObserver

/-!
# Gauge reduction: quotient the redundant symmetry, keep the effective one

`Integration.SymmetryReduction.EquivariantQuotient` says *that* a projection
intertwines two actions.  It does not distinguish the two very different things
one may mean by "symmetry reduction":

* an **orbit quotient** `X → X/G`, where the acting symmetry necessarily
  disappears downstairs — if `π` is constant on `G`-orbits and onto, then the
  induced coarse action is forced to be trivial (`coarse_action_trivial_of_orbit`);
* a **gauge reduction** `X → X/H` for a distinguished subgroup `H ≤ G` mapping
  into the kernel of `G ↠ Q`, where `H` is the redundant (gauge) direction that
  is quotiented away while the effective symmetry `Q = G/H` survives and can act
  nontrivially on the reduced carrier.

This file gives the second pattern a structure.

* `GaugeQuotient G H Q` — a monoid map `incl : H → G`, a surjective monoid map
  `quot : G → Q`, and `quot ∘ incl = 1`.  `GaugeQuotient.Exact` is the extra
  property that the kernel of `quot` is exactly the image of `incl`, i.e. that
  `Q` really is `G/H` and not a further quotient.
* `GaugeReduction G H Q Rich Coarse` — a `G`-action upstairs, a `Q`-action
  downstairs, and the square `red (g · x) = quot g · red x`.  The gauge
  subgroup is then automatically invisible downstairs (`gauge_invariant`).
* `toEquivariantQuotient` — every gauge reduction is an equivariant quotient for
  the full group `G`, so the entire welded library (`StructuredObserver`,
  `ObserverTower`, `ObserverDescent`) applies to it unchanged.
* `coarse_action_trivial_of_orbit` — the inevitability result: quotienting by
  *all* of `G` kills the downstairs action.  So a nontrivial effective action is
  possible only for a proper gauge subgroup, and `effective_not_orbit_quotient`
  turns this around: an effective reduction is provably not an orbit quotient.
* `redundant_iff_gauge` — under exactness and downstairs faithfulness, the
  symmetries invisible to the coarse layer are *exactly* the gauge subgroup.
* `compGauge` — gauge reductions compose, with the composite gauge group still
  containing the first one's.
* `toResidualQuotient` — residual support: a gauge reduction whose fibres are
  labelled by a retained residual is a `ResidualQuotient`, so it is reopenable
  and the usual cardinality bound applies.

Everything here is about arbitrary monoid actions; no finiteness is used.
-/

namespace Integration.Gauge

open Integration.SymmetryReduction
open Integration.Residual

/-! ## The algebraic datum: `H → G ↠ Q` -/

/-- A **gauge quotient** of symmetries: a monoid map `incl : H → G` picking out
the redundant directions, and a surjective monoid map `quot : G → Q` killing
them.  `Exact` below asks that nothing more is killed, which is the statement
`Q ≅ G/H`. -/
structure GaugeQuotient (G H Q : Type) [Monoid G] [Monoid H] [Monoid Q] where
  /-- The gauge subgroup, as a map into the full symmetry. -/
  incl : H → G
  /-- `incl` is unital. -/
  incl_one : incl 1 = 1
  /-- `incl` is multiplicative. -/
  incl_mul : ∀ a b, incl (a * b) = incl a * incl b
  /-- The projection onto the effective symmetry. -/
  quot : G → Q
  /-- `quot` is unital. -/
  quot_one : quot 1 = 1
  /-- `quot` is multiplicative. -/
  quot_mul : ∀ a b, quot (a * b) = quot a * quot b
  /-- Every effective symmetry lifts. -/
  quot_surjective : Function.Surjective quot
  /-- The gauge directions are killed. -/
  quot_incl : ∀ h, quot (incl h) = 1

namespace GaugeQuotient

variable {G H Q : Type} [Monoid G] [Monoid H] [Monoid Q]

/-- **Exactness**: the kernel of `quot` is no bigger than the gauge subgroup, so
`Q` is exactly `G/H` rather than a further quotient of it. -/
def Exact (P : GaugeQuotient G H Q) : Prop := ∀ g, P.quot g = 1 → ∃ h, g = P.incl h

end GaugeQuotient

/-! ## The reduction -/

/-- A **gauge reduction**: the rich carrier is acted on by the full symmetry
`G`, the coarse carrier only by the effective symmetry `Q`, and the projection
intertwines them along `quot`.  The gauge subgroup `H` is then invisible
downstairs by construction. -/
structure GaugeReduction (G H Q Rich Coarse : Type) [Monoid G] [Monoid H] [Monoid Q] where
  /-- The symmetry datum `H → G ↠ Q`. -/
  gq : GaugeQuotient G H Q
  /-- The full symmetry acting on the rich carrier. -/
  actRich : G → Rich → Rich
  /-- Unitality upstairs. -/
  rich_one : ∀ x, actRich 1 x = x
  /-- Multiplicativity upstairs. -/
  rich_mul : ∀ g g' x, actRich (g * g') x = actRich g (actRich g' x)
  /-- The effective symmetry acting on the coarse carrier. -/
  actCoarse : Q → Coarse → Coarse
  /-- Unitality downstairs. -/
  coarse_one : ∀ y, actCoarse 1 y = y
  /-- Multiplicativity downstairs. -/
  coarse_mul : ∀ q q' y, actCoarse (q * q') y = actCoarse q (actCoarse q' y)
  /-- The reduction map. -/
  red : Rich → Coarse
  /-- It is onto. -/
  red_surjective : Function.Surjective red
  /-- The commuting square, along `quot`. -/
  square : ∀ g x, red (actRich g x) = actCoarse (gq.quot g) (red x)

namespace GaugeReduction

variable {G H Q Rich Coarse : Type} [Monoid G] [Monoid H] [Monoid Q]

/-- **The gauge directions are invisible.**  Acting by the redundant subgroup
does not move the reduced state. -/
theorem gauge_invariant (R : GaugeReduction G H Q Rich Coarse) (h : H) (x : Rich) :
    R.red (R.actRich (R.gq.incl h) x) = R.red x := by
  rw [R.square, R.gq.quot_incl, R.coarse_one]

/-- Every gauge reduction is an equivariant quotient for the full symmetry, with
the coarse action factoring through `Q`.  So the welded observer library applies
to gauge reductions verbatim. -/
def toEquivariantQuotient (R : GaugeReduction G H Q Rich Coarse) :
    EquivariantQuotient G Rich Coarse where
  actRich := R.actRich
  actCoarse := fun g => R.actCoarse (R.gq.quot g)
  proj := R.red
  rich_one := R.rich_one
  rich_mul := R.rich_mul
  coarse_one := fun y => by rw [R.gq.quot_one, R.coarse_one]
  coarse_mul := fun g g' y => by rw [R.gq.quot_mul, R.coarse_mul]
  proj_surjective := R.red_surjective
  square := R.square

@[simp] theorem toEquivariantQuotient_proj (R : GaugeReduction G H Q Rich Coarse) (x : Rich) :
    R.toEquivariantQuotient.proj x = R.red x := rfl

@[simp] theorem toEquivariantQuotient_actRich (R : GaugeReduction G H Q Rich Coarse)
    (g : G) (x : Rich) : R.toEquivariantQuotient.actRich g x = R.actRich g x := rfl

/-- The reduction is **effective** if the surviving symmetry really moves the
reduced carrier. -/
def Effective (R : GaugeReduction G H Q Rich Coarse) : Prop := ∃ q y, R.actCoarse q y ≠ y

/-! ### Orbit quotients kill the symmetry -/

variable {Rich' Coarse' : Type}

/-- **Quotienting by the whole group leaves nothing acting.**  If the projection
of an equivariant quotient is constant on `G`-orbits — that is, if the coarse
layer is the orbit space — then the induced coarse action is trivial.  This is
why one should not look for a nontrivial residual action on a full orbit
quotient: `[g · x] = [x]` forces `ḡ · [x] = [x]`. -/
theorem coarse_action_trivial_of_orbit (P : EquivariantQuotient G Rich Coarse)
    (horb : ∀ g x, P.proj (P.actRich g x) = P.proj x) (g : G) (y : Coarse) :
    P.actCoarse g y = y := by
  obtain ⟨x, rfl⟩ := P.proj_surjective y
  rw [← P.square, horb]

/-- **Contrapositive: an effective reduction is not an orbit quotient.**  If some
surviving symmetry moves the coarse layer, then the reduction cannot be constant
on the orbits of the full group. -/
theorem effective_not_orbit_quotient (R : GaugeReduction G H Q Rich Coarse)
    (heff : R.Effective) : ∃ g x, R.red (R.actRich g x) ≠ R.red x := by
  obtain ⟨q, y, hq⟩ := heff
  obtain ⟨g, rfl⟩ := R.gq.quot_surjective q
  obtain ⟨x, rfl⟩ := R.red_surjective y
  exact ⟨g, x, by rw [R.square]; exact hq⟩

/-- The effective action is determined by its effect downstairs; this is the
faithfulness hypothesis used to identify the invisible symmetries. -/
def CoarseFaithful (R : GaugeReduction G H Q Rich Coarse) : Prop :=
  ∀ q, (∀ y, R.actCoarse q y = y) → q = 1

/-- **The invisible symmetries are exactly the gauge subgroup.**  If the
effective action is faithful and the symmetry datum is exact, then a symmetry
leaves every reduced state fixed if and only if it comes from `H`.  This is the
precise sense in which the reduction removes a redundancy and nothing else. -/
theorem redundant_iff_gauge (R : GaugeReduction G H Q Rich Coarse)
    (hex : R.gq.Exact) (hfaith : R.CoarseFaithful) (g : G) :
    (∀ x, R.red (R.actRich g x) = R.red x) ↔ ∃ h, g = R.gq.incl h := by
  constructor
  · intro hg
    refine hex g (hfaith _ fun y => ?_)
    obtain ⟨x, rfl⟩ := R.red_surjective y
    rw [← R.square]; exact hg x
  · rintro ⟨h, rfl⟩
    exact fun x => R.gauge_invariant h x

/-! ### Composition -/

/-- **Gauge reductions compose.**  A gauge reduction `Rich ↠ Mid` for `H ≤ G`
with effective symmetry `Q`, followed by a gauge reduction `Mid ↠ Coarse` for
`K ≤ Q` with effective symmetry `P`, is a gauge reduction `Rich ↠ Coarse` whose
gauge subgroup still contains the first one: more of the symmetry has become
redundant, none of it has come back. -/
def compGauge {Mid K P : Type} [Monoid K] [Monoid P]
    (A : GaugeReduction G H Q Rich Mid) (B : GaugeReduction Q K P Mid Coarse)
    (hmid : ∀ q y, B.actRich q y = A.actCoarse q y) :
    GaugeReduction G H P Rich Coarse where
  gq :=
    { incl := A.gq.incl
      incl_one := A.gq.incl_one
      incl_mul := A.gq.incl_mul
      quot := fun g => B.gq.quot (A.gq.quot g)
      quot_one := by rw [A.gq.quot_one, B.gq.quot_one]
      quot_mul := fun a b => by rw [A.gq.quot_mul, B.gq.quot_mul]
      quot_surjective := B.gq.quot_surjective.comp A.gq.quot_surjective
      quot_incl := fun h => by rw [A.gq.quot_incl, B.gq.quot_one] }
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

@[simp] theorem compGauge_red {Mid K P : Type} [Monoid K] [Monoid P]
    (A : GaugeReduction G H Q Rich Mid) (B : GaugeReduction Q K P Mid Coarse)
    (hmid : ∀ q y, B.actRich q y = A.actCoarse q y) (x : Rich) :
    (compGauge A B hmid).red x = B.red (A.red x) := rfl

/-- **What the composite makes redundant.**  A symmetry is invisible to the
composite coarse layer as soon as its image in the middle symmetry lies in the
second gauge subgroup. -/
theorem compGauge_invisible_of_mid_gauge {Mid K P : Type} [Monoid K] [Monoid P]
    (A : GaugeReduction G H Q Rich Mid) (B : GaugeReduction Q K P Mid Coarse)
    (hmid : ∀ q y, B.actRich q y = A.actCoarse q y) {g : G} {k : K}
    (hk : A.gq.quot g = B.gq.incl k) (x : Rich) :
    (compGauge A B hmid).red ((compGauge A B hmid).actRich g x)
      = (compGauge A B hmid).red x := by
  show B.red (A.red (A.actRich g x)) = B.red (A.red x)
  rw [A.square, ← hmid, hk]
  exact B.gauge_invariant k (A.red x)

/-- **And conversely.**  If the second stage is exact with a faithful effective
action, the symmetries invisible to the composite coarse layer are exactly those
whose image in the middle symmetry is a second-stage gauge element: the
composite gauge subgroup is the preimage of the second one. -/
theorem compGauge_redundant_iff {Mid K P : Type} [Monoid K] [Monoid P]
    (A : GaugeReduction G H Q Rich Mid) (B : GaugeReduction Q K P Mid Coarse)
    (hmid : ∀ q y, B.actRich q y = A.actCoarse q y) (hex : B.gq.Exact)
    (hfaith : B.CoarseFaithful) (g : G) :
    (∀ x, (compGauge A B hmid).red ((compGauge A B hmid).actRich g x)
        = (compGauge A B hmid).red x)
      ↔ ∃ k, A.gq.quot g = B.gq.incl k := by
  constructor
  · intro hg
    refine (B.redundant_iff_gauge hex hfaith (A.gq.quot g)).mp fun y => ?_
    obtain ⟨x, rfl⟩ := A.red_surjective y
    have hx := hg x
    rw [hmid]
    show B.red (A.actCoarse (A.gq.quot g) (A.red x)) = B.red (A.red x)
    rw [← A.square]
    exact hx
  · rintro ⟨k, hk⟩
    exact fun x => compGauge_invisible_of_mid_gauge A B hmid hk x

/-! ### Residual support -/

/-- Residual support: a gauge reduction together with a label for the points of
each fibre is a `ResidualQuotient`, hence reopenable, hence subject to the
cardinality bound "what the reduction stops showing is paid for in residual". -/
def toResidualQuotient {Res : Type} (R : GaugeReduction G H Q Rich Coarse)
    (residual : Rich → Res) (reopen : Coarse → Res → Rich)
    (hre : ∀ x, reopen (R.red x) (residual x) = x) : ResidualQuotient Rich Coarse Res where
  project := R.red
  residual := residual
  reopen := reopen
  reopen_project := hre

/-- The retained residual of a gauge reduction is nontrivial as soon as the
reduction actually loses states. -/
theorem residual_nontrivial_of_card {Res : Type} [Fintype Rich] [Fintype Coarse] [Fintype Res]
    (R : GaugeReduction G H Q Rich Coarse) (residual : Rich → Res)
    (reopen : Coarse → Res → Rich) (hre : ∀ x, reopen (R.red x) (residual x) = x)
    (hcard : Fintype.card Coarse < Fintype.card Rich) : 2 ≤ Fintype.card Res :=
  residual_not_subsingleton (R.toResidualQuotient residual reopen hre) hcard

end GaugeReduction

end Integration.Gauge
