import Mathlib

namespace PNPWindowFractran

-- Tags are distinct primes after an injective prime realization. We work
-- on square-free support at reachable boundary and private-phase states.
inductive Tag (Q I A : Type*)
  | ctrl : Q → I → Tag Q I A
  | cell : I → A → Tag Q I A
  | phase : Q → I → A → Tag Q I A
  | escape : Tag Q I A
  deriving DecidableEq

structure Config (Q I A : Type*) where
  control : Q
  head : I
  tape : I → A

structure Rule (Q I A : Type*) where
  target : Q
  write : A
  move : I → Option I

variable {Q I A : Type*}
variable [DecidableEq Q] [DecidableEq I] [DecidableEq A]

def encode (c : Config Q I A) : Set (Tag Q I A) :=
  {t | match t with
    | .ctrl q i => q=c.control ∧ i=c.head
    | .cell i a => a=c.tape i
    | _ => False}

def prepare (c : Config Q I A) : Set (Tag Q I A) :=
  {t | match t with
    | .cell i a => i≠c.head ∧ a=c.tape i
    | .phase q i a => q=c.control ∧ i=c.head ∧ a=c.tape c.head
    | _ => False}

def enabled (s den : Set (Tag Q I A)) : Prop := den ⊆ s

def raw (s num den : Set (Tag Q I A)) : Set (Tag Q I A) :=
  (s \ den) ∪ num

def readDen (q : Q) (i : I) (a : A) : Set (Tag Q I A) :=
  {Tag.ctrl q i, Tag.cell i a}

def readNum (q : Q) (i : I) (a : A) : Set (Tag Q I A) :=
  {Tag.phase q i a}

theorem read_enabled (c : Config Q I A) (q : Q) (i : I) (a : A) :
    enabled (encode c) (readDen q i a) ↔
      q=c.control ∧ i=c.head ∧ a=c.tape c.head := by
  simp [enabled,readDen,encode,Set.insert_subset_iff,Set.singleton_subset_iff]
  aesop

theorem read_not_enabled_mid (c : Config Q I A) (q : Q) (i : I) (a : A) :
    ¬ enabled (prepare c) (readDen q i a) := by
  simp [enabled,readDen,prepare,Set.insert_subset_iff]

theorem phase_not_enabled_boundary (c : Config Q I A) (q : Q) (i : I) (a : A) :
    ¬ enabled (encode c) (readNum q i a) := by
  simp [enabled,readNum,encode]

theorem phase_enabled_mid (c : Config Q I A) (q : Q) (i : I) (a : A) :
    enabled (prepare c) (readNum q i a) ↔
      q=c.control ∧ i=c.head ∧ a=c.tape c.head := by
  simp [enabled,readNum,prepare]

theorem read_exact (c : Config Q I A) :
    raw (encode c) (readNum c.control c.head (c.tape c.head))
      (readDen c.control c.head (c.tape c.head)) = prepare c := by
  ext t
  cases t <;> simp [raw,encode,readNum,readDen,prepare] <;> aesop

def writeNum (r : Rule Q I A) (i : I) : Set (Tag Q I A) :=
  {Tag.cell i r.write,
    match r.move i with
    | none => Tag.escape
    | some j => Tag.ctrl r.target j}

def update (c : Config Q I A) (r : Rule Q I A) (j : I) : Config Q I A :=
  ⟨r.target,j,Function.update c.tape c.head r.write⟩

theorem write_exact (c : Config Q I A) (r : Rule Q I A) (j : I)
    (h : r.move c.head = some j) :
    raw (prepare c) (writeNum r c.head)
      (readNum c.control c.head (c.tape c.head)) = encode (update c r j) := by
  ext t
  cases t <;> simp [raw,prepare,writeNum,readNum,encode,update,h,Function.update] <;> aesop

theorem write_escape (c : Config Q I A) (r : Rule Q I A)
    (h : r.move c.head = none) :
    Tag.escape ∈ raw (prepare c) (writeNum r c.head)
      (readNum c.control c.head (c.tape c.head)) := by
  simp [raw,writeNum,h]

-- For a deterministic table, every compiled key that can be enabled is
-- the unique original table entry. No cancellation of unchanged reads.
theorem selected_unique (table : Q → A → Option (Rule Q I A))
    (c : Config Q I A) (q : Q) (i : I) (a : A) (r : Rule Q I A)
    (entry : table q a = some r)
    (active : enabled (encode c) (readDen q i a)) :
    table c.control (c.tape c.head) = some r := by
  obtain ⟨hq,hi,ha⟩ := (read_enabled c q i a).mp active
  simpa [hq,ha] using entry

theorem two_stage (c : Config Q I A) (r : Rule Q I A) (j : I)
    (h : r.move c.head = some j) :
    raw (raw (encode c) (readNum c.control c.head (c.tape c.head))
      (readDen c.control c.head (c.tape c.head)))
      (writeNum r c.head) (readNum c.control c.head (c.tape c.head)) =
      encode (update c r j) := by
  rw [read_exact,write_exact c r j h]

-- Static window specialization is NOT a fixed source-program clock
-- improvement: it uses two raw steps per source step and code grows
-- with the supplied window. The same-object quotation still needs a
-- separately justified representation and resource bound.
end PNPWindowFractran
