import RequestProject.Kinship

/-!
# Alternative parenting: many parents, adoption, step-parents, surrogacy, donors

`RequestProject.Kinship` models the two properties Wikidata uses for the *classical*
nuclear family — `father` (P22) and `mother` (P25) — and its validator therefore
gives every person **at most two parents**, one of each.  Wikidata itself is more
liberal than that: besides P22 and P25 it has the gender-neutral `parent` (P8810),
the `stepparent` property (P3448), and the general `relative` (P1038) qualified by
`kinship to subject` (P1039), so that adoptive parents, foster parents, legal
guardians, surrogate mothers, gamete donors and godparents can all be recorded, and
so that a child can perfectly well have three or four recorded parents.

This file adds that layer.  A `ParentingKB` is a `KB` together with a list of **role-tagged
parenthood edges**

* a `child` and a `parent`, as before,
* a `ParentRole` — biological, gamete donor, surrogate, adoptive, step, foster,
  legal guardian, godparent — each grounded in the Wikidata item naming it, and
* a `ParentSlot` — `father` (P22), `mother` (P25) or the gender-neutral `parent`
  (P8810) — recording which Wikidata property carries the statement,

together with `spouse` (P26) statements.

The point of the role tag is that the different kinds of parenthood obey different
laws, and the layer keeps them apart:

* **genetic** parenthood (biological parents and gamete donors) is still limited to
  one genetic father and one genetic mother, so a person has at most two genetic
  parents (`ParentingKB.card_geneticParentsF_le_two`), and genetic ancestry is a partial
  order and well founded (`ParentingKB.geneticProperAncestor_trans`,
  `ParentingKB.geneticProperAncestor_asymm`, `ParentingKB.properAncestor_wf`);
* **any** parenthood is unbounded: the recorded parents of a person are as many as
  the sources say (`ParentingKB.rainbow_four_parents`, `ParentingKB.blended_five_parents`);
* **legal** parenthood (biological, adoptive, guardian) and **social** parenthood
  (which adds step- and foster parents) are computed separately, and neither has to
  agree with the genetic one — after an adoption they can be disjoint
  (`ParentingKB.adoption_legal_disjoint_genetic`);
* a **surrogate** carries a child she is not genetically related to, so the person
  who gave birth (`ParentingKB.gestationalParent?`) need not be a genetic parent
  (`ParentingKB.surrogacy_birth_not_genetic`).

Everything is computable and the reachability computations are certified:
`ParentingKB.descendsFromB_iff` and `ParentingKB.geneticDescendsFromB_iff` say that the Boolean
checks decide the reflexive–transitive closures of the asserted edges.

Finally the classical layer embeds: `FKB.toParentingKB` tags every P22/P25 statement as
biological, `FKB.toParentingKB_parentsL` shows the derived parents are unchanged, and
`FKB.pValid_toParentingKB` shows a validated kinship layer becomes a validated parenting
layer.  So this file is a conservative extension of `RequestProject.Kinship`.
-/

namespace Wikidata

/-- The way in which somebody is a parent of somebody else.

Wikidata records these distinctions with the qualifier `object of statement has
role` (P3831) on `parent` (P8810), with `stepparent` (P3448), or with `relative`
(P1038) qualified by `kinship to subject` (P1039); `ParentRole.entity` names the
Wikidata item each role refers to. -/
inductive ParentRole where
  /-- A biological parent (Q1502246): the child descends genetically from them. -/
  | biological
  /-- A gamete donor (Q12338229, `sperm donor`; the oocyte case is `egg donation`,
  Q1115376).  Genetically a parent, socially and legally not one. -/
  | donor
  /-- A surrogate mother (Q16547118), who carries and gives birth to the child of
  another party.  In gestational surrogacy (Q136875493) — the case modelled here —
  she is not genetically related to the child. -/
  | surrogate
  /-- An adoptive parent (Q20746742). -/
  | adoptive
  /-- A stepparent (Q19822352): the spouse of a parent, who is not themselves a
  biological parent of the child. -/
  | step
  /-- A foster parent (Q2427941), who raises a child that is neither their natural
  nor their adoptive child. -/
  | foster
  /-- A legal guardian (Q157509). -/
  | guardian
  /-- A godparent (Q223973). -/
  | godparent
deriving DecidableEq, Repr, Inhabited

namespace ParentRole

/-- The Wikidata item that names this role. -/
def entity : ParentRole → String
  | biological => "Q1502246"
  | donor => "Q12338229"
  | surrogate => "Q16547118"
  | adoptive => "Q20746742"
  | step => "Q19822352"
  | foster => "Q2427941"
  | guardian => "Q157509"
  | godparent => "Q223973"

/-- Every role. -/
def all : List ParentRole :=
  [biological, donor, surrogate, adoptive, step, foster, guardian, godparent]

theorem mem_all (r : ParentRole) : r ∈ all := by cases r <;> simp [all]

/-- The roles that make the parent a **genetic** parent of the child: the
biological parents and the gamete donors. -/
def isGenetic : ParentRole → Bool
  | biological | donor => true
  | _ => false

/-- The roles that make the parent a **legal** parent (Q66363655) of the child.
Step-parents, foster parents, surrogates, donors and godparents are not legal
parents of the child in this model; guardians (Q157509) are treated as legal
parents because they hold parental authority. -/
def isLegal : ParentRole → Bool
  | biological | adoptive | guardian => true
  | _ => false

/-- The roles under which the parent actually **raises** the child: legal parents
together with step- and foster parents. -/
def isSocial : ParentRole → Bool
  | biological | adoptive | step | foster | guardian => true
  | _ => false

end ParentRole

/-- Which Wikidata property carries a parenthood statement. -/
inductive ParentSlot where
  /-- `father` (P22). -/
  | father
  /-- `mother` (P25). -/
  | mother
  /-- The gender-neutral `parent` (P8810). -/
  | parent
deriving DecidableEq, Repr, Inhabited

namespace ParentSlot

/-- The Wikidata property this slot stands for. -/
def property : ParentSlot → String
  | father => "P22"
  | mother => "P25"
  | parent => "P8810"

/-- The two *gendered* slots, the ones a genetic parenthood statement must use. -/
def isGendered : ParentSlot → Bool
  | father | mother => true
  | parent => false

end ParentSlot

/-- One role-tagged parenthood statement. -/
structure ParentEdge where
  /-- The child. -/
  child : Qid
  /-- The parent. -/
  parent : Qid
  /-- How they are a parent. -/
  role : ParentRole := ParentRole.biological
  /-- Which Wikidata property records the statement. -/
  slot : ParentSlot := ParentSlot.parent
deriving DecidableEq, Repr, Inhabited

/-- A knowledge base together with a **parenting layer**: role-tagged parenthood
statements and `spouse` (P26) statements.  Unlike `FKB`, a person may have any
number of parents. -/
structure ParentingKB where
  /-- The underlying ontology. -/
  base : KB
  /-- The role-tagged parenthood statements. -/
  edges : List ParentEdge := []
  /-- `spouse` (P26) statements; the relation is understood symmetrically. -/
  spouses : List (Qid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace ParentingKB

variable (k : ParentingKB)

/-! ### The computational engine -/

/-- The parenthood statements about a given child. -/
def edgesOf (c : Qid) : List ParentEdge := k.edges.filter (fun e => e.child == c)

/-- All recorded parents of a person, in the order the statements were given. -/
def parentsL (c : Qid) : List Qid := (k.edgesOf c).map ParentEdge.parent

/-- All recorded parents of a person, as a `Finset`. -/
def parentsF (c : Qid) : Finset Qid := (k.parentsL c).toFinset

/-- The parents of a person whose role satisfies `pred`. -/
def parentsWithL (pred : ParentRole → Bool) (c : Qid) : List Qid :=
  ((k.edgesOf c).filter (fun e => pred e.role)).map ParentEdge.parent

/-- The genetic parents of a person: the biological parents and the donors. -/
def geneticParentsL (c : Qid) : List Qid := k.parentsWithL ParentRole.isGenetic c

/-- The genetic parents of a person, as a `Finset`. -/
def geneticParentsF (c : Qid) : Finset Qid := (k.geneticParentsL c).toFinset

/-- The legal parents of a person. -/
def legalParentsL (c : Qid) : List Qid := k.parentsWithL ParentRole.isLegal c

/-- The parents who raise the person. -/
def socialParentsL (c : Qid) : List Qid := k.parentsWithL ParentRole.isSocial c

/-- The parents recorded in a given slot (P22, P25 or P8810). -/
def slotParentsL (s : ParentSlot) (c : Qid) : List Qid :=
  ((k.edgesOf c).filter (fun e => e.slot == s)).map ParentEdge.parent

/-- The parents recorded with a given role. -/
def roleParentsL (r : ParentRole) (c : Qid) : List Qid :=
  ((k.edgesOf c).filter (fun e => e.role == r)).map ParentEdge.parent

/-- The roles under which `pa` is recorded as a parent of `c`. -/
def rolesOfL (c pa : Qid) : List ParentRole :=
  ((k.edges.filter (fun e => e.child == c && e.parent == pa)).map ParentEdge.role).dedup

/-- Decides whether `pa` is a parent of `c` under the role `r`. -/
def hasRoleB (c pa : Qid) (r : ParentRole) : Bool :=
  k.edges.any (fun e => e.child == c && e.parent == pa && e.role == r)

/-- The recorded children of a person, among the items. -/
def childrenL (pa : Qid) : List Qid := k.base.items.filter (fun c => pa ∈ k.parentsL c)

/-- The recorded children of a person under a given role. -/
def roleChildrenL (r : ParentRole) (pa : Qid) : List Qid :=
  k.base.items.filter (fun c => k.hasRoleB c pa r)

/-- The person who gave birth to `c`: the surrogate if one is recorded, and
otherwise the biological mother. -/
def gestationalParent? (c : Qid) : Option Qid :=
  match k.edges.find? (fun e => e.child == c && e.role == ParentRole.surrogate) with
  | some e => some e.parent
  | none =>
    (k.edges.find?
      (fun e => e.child == c && e.role == ParentRole.biological &&
        e.slot == ParentSlot.mother)).map ParentEdge.parent

/-- All ancestors of a person along parenthood statements **of any role**
(themselves included). -/
def ancestorClosure (c : Qid) : Finset Qid := Reach.reach k.parentsF k.base.allF c

/-- All **genetic** ancestors of a person (themselves included). -/
def geneticAncestorClosure (c : Qid) : Finset Qid :=
  Reach.reach k.geneticParentsF k.base.allF c

/-- Decides (reflexive) descent along parenthood statements of any role. -/
def descendsFromB (a b : Qid) : Bool := b ∈ k.ancestorClosure a

/-- Decides (reflexive) **genetic** descent. -/
def geneticDescendsFromB (a b : Qid) : Bool := b ∈ k.geneticAncestorClosure a

/-- Decides *proper* ancestry along statements of any role. -/
def isProperAncestorB (b a : Qid) : Bool := k.descendsFromB a b && a != b

/-- Decides *proper* genetic ancestry. -/
def isGeneticProperAncestorB (b a : Qid) : Bool := k.geneticDescendsFromB a b && a != b

/-- The ancestors of a person, among the items (themselves included). -/
def ancestorsL (a : Qid) : List Qid := k.base.items.filter (fun b => k.descendsFromB a b)

/-- The genetic ancestors of a person, among the items (themselves included). -/
def geneticAncestorsL (a : Qid) : List Qid :=
  k.base.items.filter (fun b => k.geneticDescendsFromB a b)

/-- The number of ancestors of a person: the measure that makes the genealogy well
founded. -/
def generationHeight (a : Qid) : ℕ := (k.ancestorClosure a).card

/-- Decides the `spouse` (P26) relation, understood symmetrically. -/
def spouseB (a b : Qid) : Bool := ((a, b) ∈ k.spouses) || ((b, a) ∈ k.spouses)

/-- Two distinct people are **siblings** when they share a parent of any role. -/
def siblingB (a b : Qid) : Bool :=
  a != b && k.base.items.any (fun pa => pa ∈ k.parentsL a && pa ∈ k.parentsL b)

/-- Two distinct people are **genetic siblings** when they share a genetic parent. -/
def geneticSiblingB (a b : Qid) : Bool :=
  a != b && k.base.items.any (fun pa => pa ∈ k.geneticParentsL a && pa ∈ k.geneticParentsL b)

/-- Two distinct people are **co-parents** when they are both parents of one and the
same child; this is `coparenting` (Q2996729), and needs no marriage. -/
def coParentB (a b : Qid) : Bool :=
  a != b && k.base.items.any (fun c => a ∈ k.parentsL c && b ∈ k.parentsL c)

/-! ### The validator -/

/-- All statements of the layer mention declared items. -/
def pWellFormed : Bool :=
  k.base.wellFormed &&
  k.edges.all (fun e => e.child ∈ k.base.items && e.parent ∈ k.base.items) &&
  k.spouses.all (fun r => r.1 ∈ k.base.items && r.2 ∈ k.base.items)

/-- Nobody is their own parent. -/
def noSelfParent : Bool := k.edges.all (fun e => e.child != e.parent)

/-- A genetic parenthood statement uses a gendered slot: `father` (P22) or `mother`
(P25), never the neutral `parent` (P8810).  This is what still limits genetic
parenthood to two people. -/
def geneticSlotsTyped : Bool :=
  k.edges.all (fun e => !e.role.isGenetic || e.slot.isGendered)

/-- Nobody has two different genetic fathers, and nobody two different genetic
mothers.  Note that *no* such restriction is placed on the other roles. -/
def singleGeneticParents : Bool :=
  k.edges.all (fun e => k.edges.all (fun e' =>
    !(e.role.isGenetic && e'.role.isGenetic && e.child == e'.child && e.slot == e'.slot) ||
      e.parent == e'.parent))

/-- The parenthood graph has no cycles. -/
def pAcyclic : Bool :=
  k.base.items.all (fun a => k.base.items.all
    (fun b => !(k.descendsFromB a b && k.descendsFromB b a) || a == b))

/-- Nobody is their own spouse. -/
def noSelfSpouse : Bool := k.spouses.all (fun r => r.1 != r.2)

/-- The genealogy is not the taxonomy: no parenthood statement is also a `subclass
of` or an `instance of` fact. -/
def noParentClassConfusion : Bool :=
  k.edges.all (fun e => !k.base.isSubclassOf e.child e.parent &&
    !k.base.isInstanceOf e.child e.parent)

/-- The checks the parenting layer has to pass, over and above validity of the
underlying ontology. -/
def pLayerValid : Bool :=
  k.pWellFormed && k.noSelfParent && k.geneticSlotsTyped && k.singleGeneticParents &&
    k.pAcyclic && k.noSelfSpouse && k.noParentClassConfusion

/-- The full validity check for a parenting layer. -/
def pValid : Bool := k.base.valid && k.pLayerValid

/-- An **optional** coherence check on step-parenthood: a stepparent (P3448) is the
spouse of a parent of the child.  It is deliberately not part of `pLayerValid`,
since Wikidata records step-parenthood also when the marriage is not recorded. -/
def stepConsistent : Bool :=
  k.edges.all (fun e => e.role != ParentRole.step ||
    k.base.items.any (fun pa => pa ∈ k.parentsL e.child && k.spouseB pa e.parent))

/-! ### Semantics -/

/-- The asserted parenthood statements, of any role, as a relation. -/
def Parent (c pa : Qid) : Prop := ∃ e ∈ k.edges, e.child = c ∧ e.parent = pa

/-- Parenthood restricted to the roles satisfying `pred`. -/
def ParentWith (pred : ParentRole → Bool) (c pa : Qid) : Prop :=
  ∃ e ∈ k.edges, e.child = c ∧ e.parent = pa ∧ pred e.role = true

/-- Genetic parenthood. -/
def GeneticParent (c pa : Qid) : Prop := k.ParentWith ParentRole.isGenetic c pa

/-- Legal parenthood. -/
def LegalParent (c pa : Qid) : Prop := k.ParentWith ParentRole.isLegal c pa

/-- Social parenthood. -/
def SocialParent (c pa : Qid) : Prop := k.ParentWith ParentRole.isSocial c pa

/-- Genetic parenthood recorded in a given slot. -/
def GeneticParentIn (s : ParentSlot) (c pa : Qid) : Prop :=
  ∃ e ∈ k.edges, e.child = c ∧ e.parent = pa ∧ e.role.isGenetic = true ∧ e.slot = s

/-- Derived descent: the reflexive–transitive closure of parenthood of any role. -/
def DescendsFrom (a b : Qid) : Prop := Relation.ReflTransGen k.Parent a b

/-- Derived genetic descent. -/
def GeneticDescendsFrom (a b : Qid) : Prop := Relation.ReflTransGen k.GeneticParent a b

variable {k}

/-! ### The derived relations compute what they should -/

theorem mem_parentsL {c pa : Qid} : pa ∈ k.parentsL c ↔ k.Parent c pa := by
  simp only [parentsL, edgesOf, List.mem_map, List.mem_filter, beq_iff_eq, Parent]
  constructor
  · rintro ⟨e, ⟨he, hc⟩, hp⟩; exact ⟨e, he, hc, hp⟩
  · rintro ⟨e, he, hc, hp⟩; exact ⟨e, ⟨he, hc⟩, hp⟩

theorem mem_parentsF {c pa : Qid} : pa ∈ k.parentsF c ↔ k.Parent c pa := by
  simpa [parentsF] using mem_parentsL

theorem mem_parentsWithL {pred : ParentRole → Bool} {c pa : Qid} :
    pa ∈ k.parentsWithL pred c ↔ k.ParentWith pred c pa := by
  simp only [parentsWithL, edgesOf, List.mem_map, List.mem_filter, beq_iff_eq, ParentWith]
  constructor
  · rintro ⟨e, ⟨⟨he, hc⟩, hr⟩, hp⟩; exact ⟨e, he, hc, hp, hr⟩
  · rintro ⟨e, he, hc, hp, hr⟩; exact ⟨e, ⟨⟨he, hc⟩, hr⟩, hp⟩

theorem mem_geneticParentsL {c pa : Qid} :
    pa ∈ k.geneticParentsL c ↔ k.GeneticParent c pa := mem_parentsWithL

theorem mem_geneticParentsF {c pa : Qid} :
    pa ∈ k.geneticParentsF c ↔ k.GeneticParent c pa := by
  simpa [geneticParentsF] using mem_geneticParentsL

theorem mem_legalParentsL {c pa : Qid} :
    pa ∈ k.legalParentsL c ↔ k.LegalParent c pa := mem_parentsWithL

theorem mem_socialParentsL {c pa : Qid} :
    pa ∈ k.socialParentsL c ↔ k.SocialParent c pa := mem_parentsWithL

/-- A parent of any distinguished kind is a parent. -/
theorem parent_of_parentWith {pred : ParentRole → Bool} {c pa : Qid}
    (h : k.ParentWith pred c pa) : k.Parent c pa := by
  obtain ⟨e, he, hc, hp, _⟩ := h; exact ⟨e, he, hc, hp⟩

theorem parent_of_geneticParent {c pa : Qid} (h : k.GeneticParent c pa) : k.Parent c pa :=
  parent_of_parentWith h

/-- A genetic parent is a legal parent unless they are only a donor. -/
theorem legalParent_of_biological {c pa : Qid}
    (h : ∃ e ∈ k.edges, e.child = c ∧ e.parent = pa ∧ e.role = ParentRole.biological) :
    k.LegalParent c pa ∧ k.GeneticParent c pa ∧ k.SocialParent c pa := by
  obtain ⟨e, he, hc, hp, hr⟩ := h
  exact ⟨⟨e, he, hc, hp, by simp [hr, ParentRole.isLegal]⟩,
    ⟨e, he, hc, hp, by simp [hr, ParentRole.isGenetic]⟩,
    ⟨e, he, hc, hp, by simp [hr, ParentRole.isSocial]⟩⟩

theorem succ_eq_parent (k : ParentingKB) : (fun u v => v ∈ k.parentsF u) = k.Parent := by
  funext u v; exact propext mem_parentsF

theorem succ_eq_geneticParent (k : ParentingKB) :
    (fun u v => v ∈ k.geneticParentsF u) = k.GeneticParent := by
  funext u v; exact propext mem_geneticParentsF

/-! ### Well-formedness -/

theorem pwf_base (h : k.pWellFormed = true) : k.base.wellFormed = true := by
  simp only [pWellFormed, Bool.and_eq_true] at h; tauto

/-- Both endpoints of a parenthood statement of a well-formed layer are items. -/
theorem pwf_parent (h : k.pWellFormed = true) {c pa : Qid} (hcp : k.Parent c pa) :
    c ∈ k.base.items ∧ pa ∈ k.base.items := by
  simp only [pWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, he, hc, hp⟩ := hcp
  have := h.1.2 e he
  exact ⟨hc ▸ this.1, hp ▸ this.2⟩

theorem parentsF_subset_allF (h : k.pWellFormed = true) (y : Qid) :
    k.parentsF y ⊆ k.base.allF := by
  intro _ hp
  simpa [KB.allF] using (pwf_parent h (mem_parentsF.1 hp)).2

theorem parentsF_eq_empty_of_not_mem (h : k.pWellFormed = true) {a : Qid}
    (ha : a ∉ k.base.items) : k.parentsF a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun _ hp => ?_
  exact ha (pwf_parent h (mem_parentsF.1 hp)).1

theorem geneticParentsF_subset_allF (h : k.pWellFormed = true) (y : Qid) :
    k.geneticParentsF y ⊆ k.base.allF := fun _ hp =>
  parentsF_subset_allF h y (mem_parentsF.2 (parent_of_geneticParent (mem_geneticParentsF.1 hp)))

theorem geneticParentsF_eq_empty_of_not_mem (h : k.pWellFormed = true) {a : Qid}
    (ha : a ∉ k.base.items) : k.geneticParentsF a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun pa hp => ?_
  exact ha (pwf_parent h (parent_of_geneticParent (mem_geneticParentsF.1 hp))).1

/-- **Certified ancestry computation** for parenthood of any role. -/
theorem descendsFromB_iff (h : k.pWellFormed = true) (a b : Qid) :
    k.descendsFromB a b = true ↔ k.DescendsFrom a b := by
  have hcl := Reach.mem_reach_iff_of_closed k.parentsF (parentsF_subset_allF h)
    (fun y hy => parentsF_eq_empty_of_not_mem h (by simpa [KB.allF] using hy)) a b
  rw [succ_eq_parent] at hcl
  simpa [descendsFromB, ancestorClosure, DescendsFrom] using hcl

/-- **Certified genetic ancestry computation**. -/
theorem geneticDescendsFromB_iff (h : k.pWellFormed = true) (a b : Qid) :
    k.geneticDescendsFromB a b = true ↔ k.GeneticDescendsFrom a b := by
  have hcl := Reach.mem_reach_iff_of_closed k.geneticParentsF (geneticParentsF_subset_allF h)
    (fun y hy => geneticParentsF_eq_empty_of_not_mem h (by simpa [KB.allF] using hy)) a b
  rw [succ_eq_geneticParent] at hcl
  simpa [geneticDescendsFromB, geneticAncestorClosure, GeneticDescendsFrom] using hcl

theorem descendsFromB_refl (k : ParentingKB) (a : Qid) : k.descendsFromB a a = true := by
  simpa [descendsFromB, ancestorClosure] using Reach.mem_reach_self k.parentsF k.base.allF a

theorem geneticDescendsFromB_refl (k : ParentingKB) (a : Qid) :
    k.geneticDescendsFromB a a = true := by
  simpa [geneticDescendsFromB, geneticAncestorClosure] using
    Reach.mem_reach_self k.geneticParentsF k.base.allF a

theorem descendsFromB_of_parent (h : k.pWellFormed = true) {c pa : Qid} (hcp : k.Parent c pa) :
    k.descendsFromB c pa = true :=
  (descendsFromB_iff h c pa).2 (Relation.ReflTransGen.single hcp)

theorem geneticDescendsFromB_of_geneticParent (h : k.pWellFormed = true) {c pa : Qid}
    (hcp : k.GeneticParent c pa) : k.geneticDescendsFromB c pa = true :=
  (geneticDescendsFromB_iff h c pa).2 (Relation.ReflTransGen.single hcp)

theorem descendsFromB_trans (h : k.pWellFormed = true) {a b c : Qid}
    (hab : k.descendsFromB a b = true) (hbc : k.descendsFromB b c = true) :
    k.descendsFromB a c = true :=
  (descendsFromB_iff h a c).2 (((descendsFromB_iff h a b).1 hab).trans
    ((descendsFromB_iff h b c).1 hbc))

theorem geneticDescendsFromB_trans (h : k.pWellFormed = true) {a b c : Qid}
    (hab : k.geneticDescendsFromB a b = true) (hbc : k.geneticDescendsFromB b c = true) :
    k.geneticDescendsFromB a c = true :=
  (geneticDescendsFromB_iff h a c).2 (((geneticDescendsFromB_iff h a b).1 hab).trans
    ((geneticDescendsFromB_iff h b c).1 hbc))

/-- **Genetic descent is descent**: a genetic ancestor is an ancestor. -/
theorem descendsFromB_of_geneticDescendsFromB (h : k.pWellFormed = true) {a b : Qid}
    (hab : k.geneticDescendsFromB a b = true) : k.descendsFromB a b = true := by
  refine (descendsFromB_iff h a b).2 ?_
  exact ((geneticDescendsFromB_iff h a b).1 hab).mono (fun _ _ hx => parent_of_geneticParent hx)

/-- Every ancestor of an item of the base is again an item of the base. -/
theorem mem_items_of_descendsFromB (h : k.pWellFormed = true) {a b : Qid}
    (ha : a ∈ k.base.items) (hab : k.descendsFromB a b = true) : b ∈ k.base.items := by
  have := (descendsFromB_iff h a b).1 hab
  induction this with
  | refl => exact ha
  | tail _ hstep _ => exact (pwf_parent h hstep).2

theorem mem_items_of_isProperAncestorB (h : k.pWellFormed = true) {a b : Qid}
    (hab : k.isProperAncestorB b a = true) : a ∈ k.base.items := by
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  by_contra ha
  have hcl : k.DescendsFrom a b := (descendsFromB_iff h a b).1 hab.1
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hcl with rfl | hgen
  · exact hab.2 rfl
  · exact ha (pwf_parent h (Relation.TransGen.head'_iff.1 hgen).choose_spec.1).1

/-! ### Ancestry is a partial order, and the genealogy is well founded -/

theorem descendsFromB_antisymm (h : k.pWellFormed = true) (hac : k.pAcyclic = true) {a b : Qid}
    (hab : k.descendsFromB a b = true) (hba : k.descendsFromB b a = true) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exfalso
    have ha : a ∈ k.base.items := mem_items_of_isProperAncestorB h (b := b) (by
      simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨hab, hne⟩)
    have hb : b ∈ k.base.items := mem_items_of_descendsFromB h ha hab
    simp only [pAcyclic, List.all_eq_true] at hac
    have := hac a ha b hb
    simp [hab, hba, hne] at this

theorem properAncestor_irrefl (k : ParentingKB) (a : Qid) : k.isProperAncestorB a a = false := by
  simp [isProperAncestorB]

theorem properAncestor_asymm (h : k.pWellFormed = true) (hac : k.pAcyclic = true) {a b : Qid}
    (hab : k.isProperAncestorB a b = true) (hba : k.isProperAncestorB b a = true) : False := by
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hba
  exact hab.2 (descendsFromB_antisymm h hac hab.1 hba.1)

theorem properAncestor_trans (h : k.pWellFormed = true) (hac : k.pAcyclic = true) {a b c : Qid}
    (hab : k.isProperAncestorB a b = true) (hbc : k.isProperAncestorB b c = true) :
    k.isProperAncestorB a c = true := by
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hbc ⊢
  refine ⟨descendsFromB_trans h hbc.1 hab.1, ?_⟩
  rintro rfl
  exact hbc.2 (descendsFromB_antisymm h hac hbc.1 hab.1)

theorem ancestorClosure_subset (h : k.pWellFormed = true) {a b : Qid}
    (hab : k.descendsFromB a b = true) : k.ancestorClosure b ⊆ k.ancestorClosure a := by
  intro c hc
  have hbc : k.descendsFromB b c = true := by simpa [descendsFromB] using hc
  simpa [descendsFromB] using descendsFromB_trans h hab hbc

theorem generationHeight_lt (h : k.pWellFormed = true) (hac : k.pAcyclic = true) {a b : Qid}
    (hab : k.isProperAncestorB b a = true) : k.generationHeight b < k.generationHeight a := by
  have hab' : k.descendsFromB a b = true := by
    simp only [isProperAncestorB, Bool.and_eq_true] at hab
    exact hab.1
  refine Finset.card_lt_card ⟨ancestorClosure_subset h hab', fun hsub => ?_⟩
  have ha : a ∈ k.ancestorClosure a := by
    simpa [descendsFromB] using descendsFromB_refl k a
  have hba : k.descendsFromB b a = true := by simpa [descendsFromB] using hsub ha
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  exact hab.2 (descendsFromB_antisymm h hac hab' hba)

/-- **The genealogy is well founded**, however many parents people have. -/
theorem properAncestor_wf (h : k.pWellFormed = true) (hac : k.pAcyclic = true) :
    WellFounded (fun b a : Qid => k.isProperAncestorB b a = true) := by
  refine Subrelation.wf (r := InvImage (· < ·) k.generationHeight) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro b a hab
  exact generationHeight_lt h hac hab

theorem not_transGen_properAncestor_self (h : k.pWellFormed = true) (hac : k.pAcyclic = true)
    (a : Qid) : ¬ Relation.TransGen (fun x y : Qid => k.isProperAncestorB x y = true) a a := by
  intro hgen
  have key : ∀ {x y : Qid},
      Relation.TransGen (fun x y : Qid => k.isProperAncestorB x y = true) x y →
      k.isProperAncestorB x y = true := by
    intro x y hxy
    induction hxy with
    | single hstep => exact hstep
    | tail _ hstep ih => exact properAncestor_trans h hac ih hstep
  have := key hgen
  simp [properAncestor_irrefl] at this

/-! ### Genetic ancestry is a strict order too -/

theorem geneticProperAncestor_irrefl (k : ParentingKB) (a : Qid) :
    k.isGeneticProperAncestorB a a = false := by
  simp [isGeneticProperAncestorB]

theorem geneticDescendsFromB_antisymm (h : k.pWellFormed = true) (hac : k.pAcyclic = true)
    {a b : Qid} (hab : k.geneticDescendsFromB a b = true)
    (hba : k.geneticDescendsFromB b a = true) : a = b :=
  descendsFromB_antisymm h hac (descendsFromB_of_geneticDescendsFromB h hab)
    (descendsFromB_of_geneticDescendsFromB h hba)

theorem geneticProperAncestor_asymm (h : k.pWellFormed = true) (hac : k.pAcyclic = true)
    {a b : Qid} (hab : k.isGeneticProperAncestorB a b = true)
    (hba : k.isGeneticProperAncestorB b a = true) : False := by
  simp only [isGeneticProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hba
  exact hab.2 (geneticDescendsFromB_antisymm h hac hab.1 hba.1)

theorem geneticProperAncestor_trans (h : k.pWellFormed = true) (hac : k.pAcyclic = true)
    {a b c : Qid} (hab : k.isGeneticProperAncestorB a b = true)
    (hbc : k.isGeneticProperAncestorB b c = true) :
    k.isGeneticProperAncestorB a c = true := by
  simp only [isGeneticProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hbc ⊢
  refine ⟨geneticDescendsFromB_trans h hbc.1 hab.1, ?_⟩
  rintro rfl
  exact hbc.2 (geneticDescendsFromB_antisymm h hac hbc.1 hab.1)

/-! ### At most two genetic parents, arbitrarily many parents -/

/-- On a validated layer a genetic parenthood statement is recorded either as
`father` (P22) or as `mother` (P25). -/
theorem geneticParentIn_of_geneticParent (hs : k.geneticSlotsTyped = true) {c pa : Qid}
    (h : k.GeneticParent c pa) :
    k.GeneticParentIn ParentSlot.father c pa ∨ k.GeneticParentIn ParentSlot.mother c pa := by
  obtain ⟨e, he, hc, hp, hr⟩ := h
  simp only [geneticSlotsTyped, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
  have := hs e he
  rcases this with hgen | hgend
  · rw [hr] at hgen; exact absurd hgen (by simp)
  · cases hslot : e.slot with
    | father => exact Or.inl ⟨e, he, hc, hp, hr, hslot⟩
    | mother => exact Or.inr ⟨e, he, hc, hp, hr, hslot⟩
    | parent => rw [hslot] at hgend; exact absurd hgend (by simp [ParentSlot.isGendered])

/-- On a validated layer the genetic parent recorded in a given slot is unique. -/
theorem geneticParentIn_unique (hsp : k.singleGeneticParents = true) {s : ParentSlot}
    {c x y : Qid} (hx : k.GeneticParentIn s c x) (hy : k.GeneticParentIn s c y) : x = y := by
  obtain ⟨e, he, hec, hep, her, hes⟩ := hx
  obtain ⟨e', he', hec', hep', her', hes'⟩ := hy
  simp only [singleGeneticParents, List.all_eq_true] at hsp
  have hb2 := hsp e he e' he'
  have hpre : (e.role.isGenetic && e'.role.isGenetic && (e.child == e'.child) &&
      (e.slot == e'.slot)) = true := by
    simp [her, her', hec, hec', hes, hes']
  rw [hpre] at hb2
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hb2
  rw [← hep, ← hep', hb2]

/-- **A person has at most two genetic parents**, however many parents they have. -/
theorem card_geneticParentsF_le_two (hs : k.geneticSlotsTyped = true)
    (hsp : k.singleGeneticParents = true) (c : Qid) : (k.geneticParentsF c).card ≤ 2 := by
  classical
  suffices hex : ∃ x y, ∀ z ∈ k.geneticParentsF c, z = x ∨ z = y by
    obtain ⟨x, y, hxy⟩ := hex
    have hsub : k.geneticParentsF c ⊆ ({x, y} : Finset Qid) := by
      intro z hz
      rcases hxy z hz with rfl | rfl <;> simp
    exact le_trans (Finset.card_le_card hsub)
      (by simpa using Finset.card_insert_le x ({y} : Finset Qid))
  by_cases hf : ∃ x, k.GeneticParentIn ParentSlot.father c x
  · by_cases hm : ∃ y, k.GeneticParentIn ParentSlot.mother c y
    · obtain ⟨x, hx⟩ := hf
      obtain ⟨y, hy⟩ := hm
      refine ⟨x, y, fun z hz => ?_⟩
      rcases geneticParentIn_of_geneticParent hs (mem_geneticParentsF.1 hz) with hz' | hz'
      · exact Or.inl (geneticParentIn_unique hsp hz' hx)
      · exact Or.inr (geneticParentIn_unique hsp hz' hy)
    · obtain ⟨x, hx⟩ := hf
      refine ⟨x, x, fun z hz => ?_⟩
      rcases geneticParentIn_of_geneticParent hs (mem_geneticParentsF.1 hz) with hz' | hz'
      · exact Or.inl (geneticParentIn_unique hsp hz' hx)
      · exact absurd ⟨z, hz'⟩ hm
  · by_cases hm : ∃ y, k.GeneticParentIn ParentSlot.mother c y
    · obtain ⟨y, hy⟩ := hm
      refine ⟨y, y, fun z hz => ?_⟩
      rcases geneticParentIn_of_geneticParent hs (mem_geneticParentsF.1 hz) with hz' | hz'
      · exact absurd ⟨z, hz'⟩ hf
      · exact Or.inl (geneticParentIn_unique hsp hz' hy)
    · refine ⟨c, c, fun z hz => ?_⟩
      rcases geneticParentIn_of_geneticParent hs (mem_geneticParentsF.1 hz) with hz' | hz'
      · exact absurd ⟨z, hz'⟩ hf
      · exact absurd ⟨z, hz'⟩ hm

/-! ### Siblings, co-parents and spouses -/

theorem sibling_symm (k : ParentingKB) (a b : Qid) : k.siblingB a b = k.siblingB b a := by
  rw [Bool.eq_iff_iff]
  simp only [siblingB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hne, pa, hp, h1, h2⟩; exact ⟨fun hx => hne hx.symm, pa, hp, h2, h1⟩
  · rintro ⟨hne, pa, hp, h1, h2⟩; exact ⟨fun hx => hne hx.symm, pa, hp, h2, h1⟩

theorem sibling_irrefl (k : ParentingKB) (a : Qid) : k.siblingB a a = false := by simp [siblingB]

theorem geneticSibling_symm (k : ParentingKB) (a b : Qid) :
    k.geneticSiblingB a b = k.geneticSiblingB b a := by
  rw [Bool.eq_iff_iff]
  simp only [geneticSiblingB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hne, pa, hp, h1, h2⟩; exact ⟨fun hx => hne hx.symm, pa, hp, h2, h1⟩
  · rintro ⟨hne, pa, hp, h1, h2⟩; exact ⟨fun hx => hne hx.symm, pa, hp, h2, h1⟩

/-- Genetic siblings are siblings. -/
theorem sibling_of_geneticSibling {a b : Qid} (h : k.geneticSiblingB a b = true) :
    k.siblingB a b = true := by
  simp only [geneticSiblingB, siblingB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at h ⊢
  obtain ⟨hne, pa, hp, h1, h2⟩ := h
  exact ⟨hne, pa, hp, mem_parentsL.2 (parent_of_geneticParent (mem_geneticParentsL.1 h1)),
    mem_parentsL.2 (parent_of_geneticParent (mem_geneticParentsL.1 h2))⟩

theorem coParent_symm (k : ParentingKB) (a b : Qid) : k.coParentB a b = k.coParentB b a := by
  rw [Bool.eq_iff_iff]
  simp only [coParentB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hne, c, hc, h1, h2⟩; exact ⟨fun hx => hne hx.symm, c, hc, h2, h1⟩
  · rintro ⟨hne, c, hc, h1, h2⟩; exact ⟨fun hx => hne hx.symm, c, hc, h2, h1⟩

theorem coParent_irrefl (k : ParentingKB) (a : Qid) : k.coParentB a a = false := by simp [coParentB]

theorem spouseB_symm (k : ParentingKB) (a b : Qid) : k.spouseB a b = k.spouseB b a := by
  simp [spouseB, Bool.or_comm]

theorem spouseB_irrefl (h : k.noSelfSpouse = true) (a : Qid) : k.spouseB a a = false := by
  simp only [noSelfSpouse, List.all_eq_true, bne_iff_ne, ne_eq] at h
  simp only [spouseB, Bool.or_self, decide_eq_false_iff_not]
  intro hmem
  exact h (a, a) hmem rfl

theorem mem_childrenL_iff {pa c : Qid} :
    c ∈ k.childrenL pa ↔ c ∈ k.base.items ∧ k.Parent c pa := by
  simp only [childrenL, List.mem_filter, decide_eq_true_eq]
  exact and_congr_right fun _ => mem_parentsL

theorem mem_ancestorsL_iff (h : k.pWellFormed = true) {a b : Qid} :
    b ∈ k.ancestorsL a ↔ b ∈ k.base.items ∧ k.DescendsFrom a b := by
  simp only [ancestorsL, List.mem_filter]
  exact and_congr_right fun _ => descendsFromB_iff h a b

theorem mem_geneticAncestorsL_iff (h : k.pWellFormed = true) {a b : Qid} :
    b ∈ k.geneticAncestorsL a ↔ b ∈ k.base.items ∧ k.GeneticDescendsFrom a b := by
  simp only [geneticAncestorsL, List.mem_filter]
  exact and_congr_right fun _ => geneticDescendsFromB_iff h a b

/-! ### Surrogacy: who gave birth -/

/-- If a surrogate is recorded, the person who gave birth is a recorded parent of the
child under the surrogate role. -/
theorem gestationalParent?_of_surrogate {c x : Qid}
    (hx : k.hasRoleB c x ParentRole.surrogate = true) :
    ∃ y, k.gestationalParent? c = some y ∧ k.hasRoleB c y ParentRole.surrogate = true := by
  simp only [hasRoleB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hx
  obtain ⟨e, he, ⟨hec, _⟩, her⟩ := hx
  have hne :
      (k.edges.find? (fun e => e.child == c && e.role == ParentRole.surrogate)) ≠ none := by
    intro hnone
    have := List.find?_eq_none.1 hnone e he
    simp [hec, her] at this
  obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.1 hne
  have hmem : e' ∈ k.edges := List.mem_of_find?_eq_some he'
  have hprop := List.find?_some he'
  simp only [Bool.and_eq_true, beq_iff_eq] at hprop
  refine ⟨e'.parent, by simp [gestationalParent?, he'], ?_⟩
  simp only [hasRoleB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨e', hmem, ⟨hprop.1, rfl⟩, hprop.2⟩

/-! ### The classical kinship layer embeds -/

end ParentingKB

namespace FKB

/-- Every classical kinship layer is a parenting layer: `father` (P22) and `mother`
(P25) statements become biological parenthood edges in the corresponding slot. -/
def toParentingKB (f : FKB) : ParentingKB where
  base := f.base
  edges :=
    f.fathers.map (fun r => ⟨r.1, r.2, ParentRole.biological, ParentSlot.father⟩) ++
      f.mothers.map (fun r => ⟨r.1, r.2, ParentRole.biological, ParentSlot.mother⟩)
  spouses := f.spouses

variable {f : FKB}

@[simp] theorem toParentingKB_base : f.toParentingKB.base = f.base := rfl

@[simp] theorem toParentingKB_spouses : f.toParentingKB.spouses = f.spouses := rfl

/-- The parents derived from the embedded layer are the parents of the original. -/
theorem toParentingKB_parentsL (c : Qid) : f.toParentingKB.parentsL c = f.parentsL c := by
  simp [ParentingKB.parentsL, ParentingKB.edgesOf, toParentingKB, FKB.parentsL,
    List.filter_append, List.filter_map, List.map_map, Function.comp_def]

/-- All parents of the embedded layer are genetic. -/
theorem toParentingKB_geneticParentsL (c : Qid) :
    f.toParentingKB.geneticParentsL c = f.parentsL c := by
  simp [ParentingKB.geneticParentsL, ParentingKB.parentsWithL, ParentingKB.edgesOf,
    toParentingKB, FKB.parentsL, List.filter_append, List.filter_map, List.map_map,
    Function.comp_def, ParentRole.isGenetic]

theorem toParentingKB_parentsF (c : Qid) : f.toParentingKB.parentsF c = f.parentsF c := by
  simp [ParentingKB.parentsF, FKB.parentsF, toParentingKB_parentsL]

theorem toParentingKB_parent_iff {c pa : Qid} :
    f.toParentingKB.Parent c pa ↔ f.Parent c pa := by
  rw [← ParentingKB.mem_parentsL, toParentingKB_parentsL, FKB.mem_parentsL]

theorem toParentingKB_geneticParent_iff {c pa : Qid} :
    f.toParentingKB.GeneticParent c pa ↔ f.Parent c pa := by
  rw [← ParentingKB.mem_geneticParentsL, toParentingKB_geneticParentsL, FKB.mem_parentsL]

theorem toParentingKB_ancestorClosure (c : Qid) :
    f.toParentingKB.ancestorClosure c = f.ancestorClosure c := by
  simp [ParentingKB.ancestorClosure, FKB.ancestorClosure,
    funext (fun x => toParentingKB_parentsF (f := f) x)]

theorem toParentingKB_descendsFromB (a b : Qid) :
    f.toParentingKB.descendsFromB a b = f.descendsFromB a b := by
  simp [ParentingKB.descendsFromB, FKB.descendsFromB, toParentingKB_ancestorClosure]

/-- The edges of the embedded layer are exactly the P22 and P25 statements. -/
theorem mem_toParentingKB_edges {e : ParentEdge} :
    e ∈ f.toParentingKB.edges ↔
      (e.role = ParentRole.biological ∧
        ((e.slot = ParentSlot.father ∧ (e.child, e.parent) ∈ f.fathers) ∨
          (e.slot = ParentSlot.mother ∧ (e.child, e.parent) ∈ f.mothers))) := by
  constructor
  · intro he
    simp only [toParentingKB, List.mem_append, List.mem_map] at he
    rcases he with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · exact ⟨rfl, Or.inl ⟨rfl, hr⟩⟩
    · exact ⟨rfl, Or.inr ⟨rfl, hr⟩⟩
  · rintro ⟨hrole, hcase⟩
    simp only [toParentingKB, List.mem_append, List.mem_map]
    rcases hcase with ⟨hslot, hmem⟩ | ⟨hslot, hmem⟩
    · exact Or.inl ⟨(e.child, e.parent), hmem, by cases e; simp_all⟩
    · exact Or.inr ⟨(e.child, e.parent), hmem, by cases e; simp_all⟩

theorem toParentingKB_pWellFormed (h : f.fWellFormed = true) :
    f.toParentingKB.pWellFormed = true := by
  have hb : f.base.wellFormed = true := FKB.fwf_base h
  simp only [ParentingKB.pWellFormed, toParentingKB_base, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨hb, ?_⟩, ?_⟩
  · intro e he
    have hpar : f.Parent e.child e.parent := by
      rcases (mem_toParentingKB_edges (f := f)).1 he with ⟨_, hcase⟩
      rcases hcase with ⟨_, hmem⟩ | ⟨_, hmem⟩
      · exact Or.inl hmem
      · exact Or.inr hmem
    have := FKB.fwf_parent h hpar
    simp [this.1, this.2]
  · intro r hr
    simp only [fWellFormed, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 r hr

theorem toParentingKB_noSelfParent (h : f.noKinClassConfusion = true) :
    f.toParentingKB.noSelfParent = true := by
  simp only [ParentingKB.noSelfParent, List.all_eq_true, bne_iff_ne, ne_eq]
  intro e he heq
  rcases (mem_toParentingKB_edges (f := f)).1 he with ⟨_, hcase⟩
  have hpar : f.Parent e.child e.parent := by
    rcases hcase with ⟨_, hmem⟩ | ⟨_, hmem⟩
    · exact Or.inl hmem
    · exact Or.inr hmem
  rw [heq] at hpar
  exact FKB.not_parent_self h _ hpar

theorem toParentingKB_geneticSlotsTyped (f : FKB) : f.toParentingKB.geneticSlotsTyped = true := by
  simp only [ParentingKB.geneticSlotsTyped, List.all_eq_true]
  intro e he
  rcases (mem_toParentingKB_edges (f := f)).1 he with ⟨_, hcase⟩
  rcases hcase with ⟨hslot, _⟩ | ⟨hslot, _⟩ <;> simp [hslot, ParentSlot.isGendered]

theorem toParentingKB_singleGeneticParents (h : f.singleParents = true) :
    f.toParentingKB.singleGeneticParents = true := by
  simp only [ParentingKB.singleGeneticParents, List.all_eq_true]
  intro e he e' he'
  rcases (mem_toParentingKB_edges (f := f)).1 he with ⟨_, hcase⟩
  rcases (mem_toParentingKB_edges (f := f)).1 he' with ⟨_, hcase'⟩
  by_cases hchild : e.child = e'.child
  · by_cases hslot : e.slot = e'.slot
    · have hpar : e.parent = e'.parent := by
        rcases hcase with ⟨hs, hmem⟩ | ⟨hs, hmem⟩ <;>
          rcases hcase' with ⟨hs', hmem'⟩ | ⟨hs', hmem'⟩
        · rw [hchild] at hmem
          exact FKB.father_unique h hmem hmem'
        · rw [hs, hs'] at hslot; exact absurd hslot (by simp)
        · rw [hs, hs'] at hslot; exact absurd hslot (by simp)
        · rw [hchild] at hmem
          exact FKB.mother_unique h hmem hmem'
      simp [hpar]
    · simp [hslot]
  · simp [hchild]

theorem toParentingKB_pAcyclic (h : f.fAcyclic = true) : f.toParentingKB.pAcyclic = true := by
  have hEq : f.toParentingKB.pAcyclic = f.fAcyclic := by
    simp [ParentingKB.pAcyclic, FKB.fAcyclic, toParentingKB_base, toParentingKB_descendsFromB]
  rw [hEq, h]

theorem toParentingKB_noSelfSpouse (h : f.noSelfSpouse = true) :
    f.toParentingKB.noSelfSpouse = true := h

theorem toParentingKB_noParentClassConfusion (h : f.noKinClassConfusion = true) :
    f.toParentingKB.noParentClassConfusion = true := by
  simp only [ParentingKB.noParentClassConfusion, List.all_eq_true, toParentingKB_base]
  intro e he
  have hpar : f.Parent e.child e.parent := by
    rcases (mem_toParentingKB_edges (f := f)).1 he with ⟨_, hcase⟩
    rcases hcase with ⟨_, hmem⟩ | ⟨_, hmem⟩
    · exact Or.inl hmem
    · exact Or.inr hmem
  simp [FKB.parent_not_subclass h hpar, FKB.parent_not_instance h hpar]

/-- **The embedding preserves validity**: a validated kinship layer becomes a
validated parenting layer.  So the parenting layer is a conservative extension of
the classical `father`/`mother` layer. -/
theorem pValid_toParentingKB (h : f.fValid = true) : f.toParentingKB.pValid = true := by
  simp only [fValid, fLayerValid, Bool.and_eq_true] at h
  obtain ⟨hbase, ⟨⟨⟨⟨hwf, hsp⟩, hac⟩, hss⟩, hkc⟩⟩ := h
  simp only [ParentingKB.pValid, ParentingKB.pLayerValid, toParentingKB_base, Bool.and_eq_true]
  exact ⟨hbase, ⟨⟨⟨⟨⟨⟨toParentingKB_pWellFormed hwf,
    toParentingKB_noSelfParent hkc⟩,
    toParentingKB_geneticSlotsTyped f⟩, toParentingKB_singleGeneticParents hsp⟩,
    toParentingKB_pAcyclic hac⟩, toParentingKB_noSelfSpouse hss⟩,
    toParentingKB_noParentClassConfusion hkc⟩⟩

end FKB

end Wikidata
