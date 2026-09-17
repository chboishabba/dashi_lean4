/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Merge

/-!
# Peer-to-peer replication: gossiping ontologies between mirrors

The project publishes the same ontology in several places — a static site, a
dataset repository, a peer-to-peer network, a long term archive.  Each of those
is a *replica*, and replicas drift: one of them learns a statement the others do
not have yet.  This file says what it means for them to come back together, and
proves that the obvious protocol works.

The protocol is the simplest one possible: **a peer that hears from another peer
imports what it heard** (`KB.sync = KB.merge`).  Two replicas are considered *in
agreement* when each entails the other (`KB.Equiv`) — that is, when they answer
every `subclass of` and `instance of` question the same way (`Merge.entails_subclass`,
`Merge.entails_instance`), even if their files list the statements in a different
order or with repetitions.

What is proved:

* `KB.sync_entails_left`, `KB.sync_entails_right` — **no loss**: a peer that syncs
  keeps everything both sides knew;
* `KB.sync_least` — syncing adds nothing else: the result is the *least* upper
  bound in the entailment preorder, so gossip cannot invent knowledge;
* `KB.sync_comm_equiv`, `KB.sync_assoc_equiv`, `KB.sync_idem_equiv`,
  `KB.sync_empty_equiv` — sync is commutative, associative and idempotent up to
  agreement: a semilattice, which is exactly the condition under which replicas
  that exchange updates in any order and any number of times converge;
* `KB.gossip_equiv_pool` and `KB.gossip_pairwise_equiv` — **strong eventual
  consistency**: after one round in which every peer imports the pooled state,
  all replicas agree, whatever they started from;
* `KB.pool_entails_mem` — and the state they agree on entails every peer's
  original contribution, so nothing any peer knew is dropped on the way.
-/

namespace Wikidata
namespace KB

/-- The empty knowledge base: what a fresh peer starts from. -/
def empty : KB := { name := "empty", items := [] }

@[simp] theorem empty_items : empty.items = [] := rfl
@[simp] theorem empty_sub : empty.sub = [] := rfl
@[simp] theorem empty_inst : empty.inst = [] := rfl
@[simp] theorem empty_disj : empty.disj = [] := rfl

theorem empty_wellFormed : empty.wellFormed = true := by decide

/-- Two replicas *agree* when each entails the other: they answer every derived
`subclass of` and `instance of` question identically. -/
def Equiv (kb kb' : KB) : Bool := kb.Entails kb' && kb'.Entails kb

/-- A peer syncing with another imports what it heard. -/
def sync (kb kb' : KB) : KB := kb.merge kb'

variable {kb kb' kb'' : KB}

theorem equiv_iff : Equiv kb kb' = true ↔ kb.Entails kb' = true ∧ kb'.Entails kb = true := by
  simp [Equiv]

theorem equiv_refl (hwf : kb.wellFormed = true) : Equiv kb kb = true :=
  equiv_iff.2 ⟨entails_refl hwf, entails_refl hwf⟩

theorem equiv_symm (h : Equiv kb kb' = true) : Equiv kb' kb = true :=
  equiv_iff.2 ⟨(equiv_iff.1 h).2, (equiv_iff.1 h).1⟩

theorem equiv_trans (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (hwf'' : kb''.wellFormed = true) (h : Equiv kb kb' = true) (h' : Equiv kb' kb'' = true) :
    Equiv kb kb'' = true :=
  equiv_iff.2 ⟨entails_trans hwf hwf' (equiv_iff.1 h).1 (equiv_iff.1 h').1,
    entails_trans hwf'' hwf' (equiv_iff.1 h').2 (equiv_iff.1 h).2⟩

/-! ### One exchange -/

theorem wellFormed_sync (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    (kb.sync kb').wellFormed = true := wellFormed_merge hwf hwf'

/-- **Nothing is lost**: after syncing, a peer still knows everything it knew. -/
theorem sync_entails_left (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    (kb.sync kb').Entails kb = true := merge_entails_left hwf hwf'

/-- **Nothing is missed**: after syncing, a peer knows everything the other knew. -/
theorem sync_entails_right (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    (kb.sync kb').Entails kb' = true := merge_entails_right hwf hwf'

/-- **Nothing is invented**: any base that already entails both peers entails the
result of their sync.  With the two lemmas above, sync is the least upper bound
for entailment. -/
theorem sync_least (h : kb''.Entails kb = true) (h' : kb''.Entails kb' = true) :
    kb''.Entails (kb.sync kb') = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true] at h h' ⊢
  constructor
  · intro p hp
    rcases List.mem_append.1 (by simpa [sync] using hp) with hp | hp
    · exact h.1 p hp
    · exact h'.1 p hp
  · intro p hp
    rcases List.mem_append.1 (by simpa [sync] using hp) with hp | hp
    · exact h.2 p hp
    · exact h'.2 p hp

/-- Sync is commutative up to agreement: it does not matter who called whom. -/
theorem sync_comm_equiv (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true) :
    Equiv (kb.sync kb') (kb'.sync kb) = true := by
  exact equiv_iff.2
    ⟨sync_least (sync_entails_right hwf hwf') (sync_entails_left hwf hwf'),
     sync_least (sync_entails_right hwf' hwf) (sync_entails_left hwf' hwf)⟩

/-- Sync is associative up to agreement: peers may pool their states in any
grouping. -/
theorem sync_assoc_equiv (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (hwf'' : kb''.wellFormed = true) :
    Equiv ((kb.sync kb').sync kb'') (kb.sync (kb'.sync kb'')) = true := by
  have h12 := wellFormed_sync hwf hwf'
  have h23 := wellFormed_sync hwf' hwf''
  have hL := wellFormed_sync h12 hwf''
  have hR := wellFormed_sync hwf h23
  -- the left grouping knows each of the three peers
  have hLa : ((kb.sync kb').sync kb'').Entails kb = true :=
    entails_trans hL h12 (sync_entails_left h12 hwf'') (sync_entails_left hwf hwf')
  have hLb : ((kb.sync kb').sync kb'').Entails kb' = true :=
    entails_trans hL h12 (sync_entails_left h12 hwf'') (sync_entails_right hwf hwf')
  have hLc : ((kb.sync kb').sync kb'').Entails kb'' = true := sync_entails_right h12 hwf''
  -- and so does the right grouping
  have hRa : (kb.sync (kb'.sync kb'')).Entails kb = true := sync_entails_left hwf h23
  have hRb : (kb.sync (kb'.sync kb'')).Entails kb' = true :=
    entails_trans hR h23 (sync_entails_right hwf h23) (sync_entails_left hwf' hwf'')
  have hRc : (kb.sync (kb'.sync kb'')).Entails kb'' = true :=
    entails_trans hR h23 (sync_entails_right hwf h23) (sync_entails_right hwf' hwf'')
  refine equiv_iff.2 ⟨?_, ?_⟩
  · exact sync_least hLa (sync_least hLb hLc)
  · exact sync_least (sync_least hRa hRb) hRc

/-- Syncing with a peer twice changes nothing: gossip may be repeated freely. -/
theorem sync_idem_equiv (hwf : kb.wellFormed = true) : Equiv (kb.sync kb) kb = true :=
  equiv_iff.2 ⟨sync_entails_left hwf hwf,
    sync_least (entails_refl hwf) (entails_refl hwf)⟩

/-- Every base entails the empty one: a fresh peer knows nothing. -/
theorem entails_empty (kb : KB) : kb.Entails empty = true := by simp [Entails]

/-- Syncing with a fresh peer changes nothing. -/
theorem sync_empty_equiv (hwf : kb.wellFormed = true) : Equiv (kb.sync empty) kb = true :=
  equiv_iff.2 ⟨sync_entails_left hwf empty_wellFormed,
    sync_least (entails_refl hwf) (entails_empty kb)⟩

/-! ### A round of gossip -/

/-- The pooled state of a network: everything all the peers together know. -/
def pool (peers : List KB) : KB := peers.foldl KB.merge empty

/-- One round of gossip: every peer imports the pooled state. -/
def gossip (peers : List KB) : List KB := peers.map (fun p => p.sync (pool peers))

theorem wellFormed_foldl_merge : ∀ (peers : List KB) (acc : KB), acc.wellFormed = true →
    (∀ p ∈ peers, p.wellFormed = true) → (peers.foldl KB.merge acc).wellFormed = true
  | [], _, hacc, _ => hacc
  | p :: ps, acc, hacc, hall => by
      refine wellFormed_foldl_merge ps (acc.merge p)
        (wellFormed_merge hacc (hall p List.mem_cons_self)) ?_
      exact fun q hq => hall q (List.mem_cons_of_mem _ hq)

theorem wellFormed_pool {peers : List KB} (h : ∀ p ∈ peers, p.wellFormed = true) :
    (pool peers).wellFormed = true :=
  wellFormed_foldl_merge peers empty empty_wellFormed h

theorem entails_foldl_acc : ∀ (peers : List KB) (acc : KB), acc.wellFormed = true →
    (∀ p ∈ peers, p.wellFormed = true) → (peers.foldl KB.merge acc).Entails acc = true
  | [], acc, hacc, _ => entails_refl hacc
  | p :: ps, acc, hacc, hall => by
      have hp := hall p List.mem_cons_self
      have hps : ∀ q ∈ ps, q.wellFormed = true := fun q hq => hall q (List.mem_cons_of_mem _ hq)
      have hm := wellFormed_merge hacc hp
      have hf := wellFormed_foldl_merge ps (acc.merge p) hm hps
      exact entails_trans hf hm (entails_foldl_acc ps (acc.merge p) hm hps)
        (merge_entails_left hacc hp)

theorem entails_foldl_mem : ∀ (peers : List KB) (acc : KB), acc.wellFormed = true →
    (∀ p ∈ peers, p.wellFormed = true) → ∀ {q : KB}, q ∈ peers →
      (peers.foldl KB.merge acc).Entails q = true
  | [], _, _, _, _, hq => absurd hq (by simp)
  | p :: ps, acc, hacc, hall, q, hq => by
      have hp := hall p List.mem_cons_self
      have hps : ∀ r ∈ ps, r.wellFormed = true := fun r hr => hall r (List.mem_cons_of_mem _ hr)
      have hm := wellFormed_merge hacc hp
      have hf := wellFormed_foldl_merge ps (acc.merge p) hm hps
      rcases List.mem_cons.1 hq with hqp | hq
      · subst hqp
        exact entails_trans hf hm (entails_foldl_acc ps (acc.merge q) hm hps)
          (merge_entails_right hacc hp)
      · exact entails_foldl_mem ps (acc.merge p) hm hps hq

/-- **The pooled state loses nothing**: it entails every peer's contribution. -/
theorem pool_entails_mem {peers : List KB} (h : ∀ p ∈ peers, p.wellFormed = true)
    {q : KB} (hq : q ∈ peers) : (pool peers).Entails q = true :=
  entails_foldl_mem peers empty empty_wellFormed h hq

/-- After a round of gossip every peer agrees with the pooled state. -/
theorem gossip_equiv_pool {peers : List KB} (h : ∀ p ∈ peers, p.wellFormed = true)
    {p : KB} (hp : p ∈ peers) : Equiv (p.sync (pool peers)) (pool peers) = true := by
  have hpw := h p hp
  have hpool := wellFormed_pool h
  have hm := wellFormed_sync hpw hpool
  refine equiv_iff.2 ⟨sync_entails_right hpw hpool, ?_⟩
  exact sync_least (pool_entails_mem h hp) (entails_refl hpool)

/-- **Strong eventual consistency**: after one round of gossip all replicas agree,
whatever states they started from. -/
theorem gossip_pairwise_equiv {peers : List KB} (h : ∀ p ∈ peers, p.wellFormed = true)
    {a b : KB} (ha : a ∈ gossip peers) (hb : b ∈ gossip peers) : Equiv a b = true := by
  simp only [gossip, List.mem_map] at ha hb
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hb
  have hpool := wellFormed_pool h
  have hpw := wellFormed_sync (h p hp) hpool
  have hqw := wellFormed_sync (h q hq) hpool
  exact equiv_trans hpw hpool hqw (gossip_equiv_pool h hp)
    (equiv_symm (gossip_equiv_pool h hq))

/-- And the state they converge on knows everything any peer knew. -/
theorem gossip_entails_all {peers : List KB} (h : ∀ p ∈ peers, p.wellFormed = true)
    {a : KB} (ha : a ∈ gossip peers) {q : KB} (hq : q ∈ peers) : a.Entails q = true := by
  simp only [gossip, List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hpool := wellFormed_pool h
  have hpw := wellFormed_sync (h p hp) hpool
  exact entails_trans hpw hpool (sync_entails_right (h p hp) hpool) (pool_entails_mem h hq)

/-- Every replica after a round of gossip is well-formed, so the certified queries
apply to it unchanged. -/
theorem gossip_wellFormed {peers : List KB} (h : ∀ p ∈ peers, p.wellFormed = true)
    {a : KB} (ha : a ∈ gossip peers) : a.wellFormed = true := by
  simp only [gossip, List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact wellFormed_sync (h p hp) (wellFormed_pool h)

end KB
end Wikidata
