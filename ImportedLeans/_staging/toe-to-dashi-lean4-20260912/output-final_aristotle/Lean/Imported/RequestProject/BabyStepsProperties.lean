import RequestProject.Properties

/-!
# Baby steps, part two: properties, one small step at a time

`RequestProject.BabySteps` built a four-item Wikidata fragment by hand and read
off the facts about `instance of` (P31) and `subclass of` (P279). This file is
its sequel: it does the same for the *property layer* of
`RequestProject.Properties`, where items are related by statements
`⟨subject, property, value⟩` and the properties themselves carry ontological
information.

As before nothing here is used by the rest of the development, every step is a
one- or two-line theorem, and the steps are numbered so they can be read in
order.

The running example is the five-item, four-property fragment

```
Douglas Adams  --P26 (spouse)--> Jane Belson        P26 ⊑ P1038 (relative), P26 symmetric
London         --P361 (part of)--> England          P361 transitive,
England        --P361 (part of)--> Europe           P361 inverse of P527 (has part)
```

Steps 0–3 assert it, steps 4–6 read off what follows, and steps 7–8 — the point
of the whole file — read off what does *not* follow, using the minimality of the
derived statement relation.
-/

namespace Wikidata
namespace BabyStepsProperties

/-! ## Step 0: five items and four properties

Just as an ontology is carried by any type of items, a property layer is carried
by any type of items and any type of properties. Ours are both finite. -/

/-- The five items of our miniature Wikidata: two people and three places. -/
inductive Item
  | adams
  | jane
  | london
  | england
  | europe
  deriving DecidableEq, Repr

/-- The four properties: `spouse` (P26), `relative` (P1038), `part of` (P361) and
`has part(s)` (P527). -/
inductive Prop'
  | spouse
  | relative
  | partOf
  | hasPart
  deriving DecidableEq, Repr

open Item Prop'

/-! ## Step 1: the asserted statements

Three statements, written as a plain predicate on ⟨property, subject, value⟩. -/

/-- Douglas Adams is the spouse of Jane Belson; London is part of England;
England is part of Europe. Nothing else is asserted. -/
def stmt : Prop' → Item → Item → Prop
  | spouse, adams, jane => True
  | partOf, london, england => True
  | partOf, england, europe => True
  | _, _, _ => False

/-! ## Step 2: what Wikidata says about the properties themselves

`spouse` is a *subproperty of* `relative` (P1647); `spouse` is declared
*symmetric* (Q18647518); `part of` is declared *transitive* (Q18647515); and
`part of` and `has part(s)` are declared *inverse* (P1696). -/

/-- The single `subproperty of` (P1647) declaration: `spouse ⊑ relative`. -/
def subProp : Prop' → Prop' → Prop
  | spouse, relative => True
  | _, _ => False

/-- `part of` is the only property declared transitive. -/
def isTrans : Prop' → Prop
  | partOf => True
  | _ => False

/-- `spouse` is the only property declared symmetric. -/
def isSymm : Prop' → Prop
  | spouse => True
  | _ => False

/-- `part of` and `has part(s)` are inverse to one another; we record the
declaration in both directions, as Wikidata does. -/
def inverse : Prop' → Prop' → Prop
  | partOf, hasPart => True
  | hasPart, partOf => True
  | _, _ => False

/-- Being inverse is symmetric — the one obligation of a `PropertyLayer`. -/
theorem inverse_symm {p q : Prop'} (h : inverse p q) : inverse q p := by
  cases p <;> cases q <;> simp_all [inverse]

/-! ## Step 3: the property layer

With that obligation discharged, the fragment *is* a property layer. -/

/-- Our miniature property layer. -/
def fam : PropertyLayer Item Prop' where
  Stmt := stmt
  SubProp := subProp
  IsTransitive := isTrans
  IsSymmetric := isSymm
  InverseOf := inverse
  inverseOf_symm := inverse_symm

/-! ## Step 4: the asserted statements are derived

`PropertyLayer.Holds` — the derived statement relation — contains at least what
we asserted. -/

/-- Douglas Adams is the spouse of Jane Belson: the statement we wrote down. -/
theorem adams_spouse_jane : fam.Holds spouse adams jane :=
  PropertyLayer.Holds.stmt trivial

/-- London is part of England: the statement we wrote down. -/
theorem london_partOf_england : fam.Holds partOf london england :=
  PropertyLayer.Holds.stmt trivial

/-- England is part of Europe: the statement we wrote down. -/
theorem england_partOf_europe : fam.Holds partOf england europe :=
  PropertyLayer.Holds.stmt trivial

/-! ## Step 5: the derived facts

Nobody asserted any of the following; each follows from one of the four rules. -/

/-- Along the property hierarchy: a spouse is a relative. -/
theorem adams_relative_jane : fam.Holds relative adams jane :=
  PropertyLayer.Holds.sub (p := spouse) trivial adams_spouse_jane

/-- By symmetry: Jane Belson is the spouse of Douglas Adams. -/
theorem jane_spouse_adams : fam.Holds spouse jane adams :=
  (PropertyLayer.holds_symm_iff (L := fam) (p := spouse) trivial adams jane).1 adams_spouse_jane

/-- The two rules combine: Jane Belson is a relative of Douglas Adams. -/
theorem jane_relative_adams : fam.Holds relative jane adams :=
  PropertyLayer.Holds.sub (p := spouse) trivial jane_spouse_adams

/-- By transitivity of `part of`: London is part of Europe. -/
theorem london_partOf_europe : fam.Holds partOf london europe :=
  PropertyLayer.Holds.trans trivial london_partOf_england england_partOf_europe

/-- By the inverse declaration, read backwards: Europe has part London. -/
theorem europe_hasPart_london : fam.Holds hasPart europe london :=
  (PropertyLayer.holds_inverse_iff (L := fam) (p := partOf) (q := hasPart)
    trivial london europe).1 london_partOf_europe

/-- And `has part(s)` inherits transitivity from its inverse, even though it was
never declared transitive itself. -/
theorem hasPart_trans {a b c : Item} (hab : fam.Holds hasPart a b)
    (hbc : fam.Holds hasPart b c) : fam.Holds hasPart a c :=
  PropertyLayer.holds_trans_of_inverse (L := fam) (p := partOf) (q := hasPart) trivial trivial hab hbc

/-! ## Step 6: how to prove that something is *not* derived

Showing that a statement does not follow is a different kind of step. It uses
the minimality of `Holds` (`PropertyLayer.holds_minimal`): to rule a statement
out it suffices to exhibit *one* relation that contains the asserted statements,
is closed under the four rules, and misses the statement in question.

Our first such relation ignores the property and only records the *kind* of the
two items. -/

/-- The two people of the fragment. -/
def isPerson : Item → Prop
  | adams | jane => True
  | _ => False

/-- The three places of the fragment. -/
def isPlace : Item → Prop
  | london | england | europe => True
  | _ => False

/-- `sameKind s o`: the items `s` and `o` are both people, or both places. -/
def sameKind (_p : Prop') (s o : Item) : Prop :=
  (isPerson s ∧ isPerson o) ∨ (isPlace s ∧ isPlace o)

/-- `sameKind` is closed under all four rules, so it over-approximates the
derived statements. -/
theorem isClosed_sameKind : PropertyLayer.IsClosed (L := fam) sameKind where
  stmt := by
    intro p s o h
    cases p <;> cases s <;> cases o <;>
      simp_all [fam, stmt, sameKind, isPerson, isPlace]
  sub := by
    intro p q s o _ h; exact h
  trans := by
    intro p a b c _ hab hbc
    cases a <;> cases b <;> cases c <;>
      simp_all [sameKind, isPerson, isPlace]
  symm := by
    intro p s o _ h
    cases s <;> cases o <;> simp_all [sameKind, isPerson, isPlace]
  inv := by
    intro p q s o _ h
    cases s <;> cases o <;> simp_all [sameKind, isPerson, isPlace]

/-- **No statement of the fragment ever links a person to a place.** In
particular London is not a relative of Jane Belson. -/
theorem no_person_place {p : Prop'} {s o : Item} (hs : isPlace s) (ho : isPerson o) :
    ¬ fam.Holds p s o := by
  intro h
  have := PropertyLayer.holds_minimal isClosed_sameKind h
  cases s <;> cases o <;> simp_all [sameKind, isPerson, isPlace]

/-- A concrete instance: London is not a relative of Jane Belson. -/
theorem london_not_relative_jane : ¬ fam.Holds relative london jane :=
  no_person_place trivial trivial

/-! ## Step 7: `part of` has no cycles here

The second closed relation *does* depend on the property: it ranks the three
places and asks that `part of` strictly increases the rank (and `has part(s)`
strictly decreases it). -/

/-- A rank for the three places; the two people are given rank `0`, which the
relation below never looks at. -/
def rank : Item → ℕ
  | london => 1
  | england => 2
  | europe => 3
  | _ => 0

/-- The married pair, in both directions. -/
def married : Item → Item → Prop
  | adams, jane => True
  | jane, adams => True
  | _, _ => False

/-- The graded over-approximation: `part of` goes strictly up the ranks,
`has part(s)` strictly down, and the two family properties relate only the
married pair. -/
def graded : Prop' → Item → Item → Prop
  | partOf, s, o => rank s < rank o
  | hasPart, s, o => rank o < rank s
  | spouse, s, o => married s o
  | relative, s, o => married s o

/-- `graded` too is closed under all four rules. -/
theorem isClosed_graded : PropertyLayer.IsClosed (L := fam) graded where
  stmt := by
    intro p s o h
    cases p <;> cases s <;> cases o <;>
      simp_all [fam, stmt, graded, married, rank]
  sub := by
    intro p q s o hpq h
    cases p <;> cases q <;> simp_all [fam, subProp, graded]
  trans := by
    intro p a b c hp hab hbc
    cases p <;> simp_all [fam, isTrans, graded]
    omega
  symm := by
    intro p s o hp h
    cases p <;> simp_all [fam, isSymm, graded]
    cases s <;> cases o <;> simp_all [married]
  inv := by
    intro p q s o hpq h
    cases p <;> cases q <;> simp_all [fam, inverse, graded]

/-- **`part of` is acyclic on the fragment**: nothing is part of something of no
greater rank. -/
theorem partOf_rank_lt {s o : Item} (h : fam.Holds partOf s o) : rank s < rank o :=
  PropertyLayer.holds_minimal isClosed_graded h

/-- In particular England is not part of London, even though London is part of
England. -/
theorem england_not_partOf_london : ¬ fam.Holds partOf england london := by
  intro h
  have := partOf_rank_lt h
  simp [rank] at this

/-- And nothing is part of itself. -/
theorem partOf_irrefl (s : Item) : ¬ fam.Holds partOf s s := fun h =>
  absurd (partOf_rank_lt h) (lt_irrefl _)

/-! ## Step 8: `relative` is not symmetric *by declaration*

We derived `jane_relative_adams` above — but only because it came from the
symmetric property `spouse`. `relative` itself is not declared symmetric, and
indeed the fragment derives no `relative` statement outside the married pair. -/

/-- Every derived `relative` statement is one of the two directions between
Douglas Adams and Jane Belson. -/
theorem relative_married {s o : Item} (h : fam.Holds relative s o) : married s o :=
  PropertyLayer.holds_minimal isClosed_graded h

/-- So, for example, England is not a relative of Europe. -/
theorem england_not_relative_europe : ¬ fam.Holds relative england europe := by
  intro h
  have := relative_married h
  simp [married] at this

end BabyStepsProperties
end Wikidata
