import RequestProject.RelationWords

/-!
# Programs as numbers, and the algebra of transformations

This module takes the *program–number correspondence* seriously for the one
class of programs this development actually has: the **transformations of the
ontology layer**, i.e. the words in the relations `subclass of` (P279) and
`instance of` (P31) that `RequestProject.RelationWords` turns into operators.

The ladder that is formalised here, and the honest scope of each rung:

| rung | what is proved |
|---|---|
| `ℕ` | **programs are numbers**: `RelWord.encode` is a bijection between words and `ℕ` (`RelWord.decode_encode`, `RelWord.encode_decode`), so every transformation of the ontology layer has a Gödel number and every number names one |
| monoid | **programs compose**: concatenation of words is composition of operators (`KB.wordStep_append`), with the empty word as unit (`KB.wordStep_nil`) |
| `ℤ` | **the grading**: the level displacement `RelWord.degree` is a monoid homomorphism to `(ℤ, +)` (`RelWord.degree_append`), and it is the metaclass level shift of the transformation in any ontology (`Ontology.level_add_degree`); the degree-zero part is where closed loops live (`Ontology.degree_eq_zero_of_closed`) |
| functoriality | **compiler stages are morphisms**: a stage that only deletes statements maps walks to walks (`KB.wordStep_mono`), so every invariant below is preserved by the repair pipeline of the defect report |
| `ZMod d` | **phases**: a component of period `d` carries a `ZMod d`-valued phase, and its return times are exactly the positive multiples of `d` (`RequestProject.Periodicity`) |
| finite periodicity | **the transformation algebra is eventually periodic**: on a finite carrier the powers of a relation repeat (`RelAlg.exists_eventually_periodic`), and for the cyclic part of the downloaded corpus the repetition is exact and computed: it is a permutation of **order exactly 12** (`CyclicAlgebra.cyclicRel_order_twelve`) |

What is **not** here, and should not be read into it: nothing in this development
produces quaternionic, octonionic or Clifford structure, and the periodicity that
does appear — 12, the least common multiple of the four component periods 2, 4,
3, 2 — has no proved connection to Bott periodicity's 8.  The rungs above `ℤ`
in the informal ladder are conjectural; the rungs formalised here are the ones
the data and the semantics actually support.
-/

namespace Wikidata

/-! ### Programs as numbers: a Gödel numbering of the relation words -/

namespace RelWord

/-- The digit of a letter in the bijective base-2 numbering: `subclass of` is the
digit 1 and `instance of` the digit 2. -/
def digit : Link → ℕ
  | .p279 => 1
  | .p31 => 2

/-- **The Gödel number of a word**, in bijective base 2: the empty word is `0`
and `l :: w` is `2 · code(w) + digit(l)`. -/
def encode : List Link → ℕ
  | [] => 0
  | l :: w => 2 * encode w + digit l

theorem encode_pos {l : Link} {w : List Link} : 0 < encode (l :: w) := by
  cases l <;> simp [encode, digit]

/-- **The word with a given Gödel number.** -/
def decode : ℕ → List Link
  | 0 => []
  | (n + 1) =>
      if (n + 1) % 2 = 1 then Link.p279 :: decode (n / 2)
      else Link.p31 :: decode ((n - 1) / 2)
  decreasing_by
    · omega
    · omega

@[simp] theorem decode_zero : decode 0 = [] := by rw [decode]

/-- **Every word is recovered from its number.** -/
theorem decode_encode (w : List Link) : decode (encode w) = w := by
  induction w with
  | nil => rw [show encode ([] : List Link) = 0 from rfl, decode_zero]
  | cons l w ih =>
      cases l with
      | p279 =>
          have hval : encode (Link.p279 :: w) = 2 * encode w + 1 := rfl
          rw [hval]
          have hne : 2 * encode w + 1 = (2 * encode w) + 1 := rfl
          rw [hne, decode]
          have h1 : (2 * encode w + 1) % 2 = 1 := by omega
          rw [if_pos h1]
          have h2 : 2 * encode w / 2 = encode w := by omega
          rw [h2, ih]
      | p31 =>
          have hval : encode (Link.p31 :: w) = 2 * encode w + 2 := rfl
          rw [hval]
          have hne : 2 * encode w + 2 = (2 * encode w + 1) + 1 := rfl
          rw [hne, decode]
          have h1 : ¬ ((2 * encode w + 1) + 1) % 2 = 1 := by omega
          rw [if_neg h1]
          have h2 : (2 * encode w + 1 - 1) / 2 = encode w := by omega
          rw [h2, ih]

/-- The numbering is injective: different programs have different numbers. -/
theorem encode_injective : Function.Injective encode := by
  intro v w h
  have := congrArg decode h
  rwa [decode_encode, decode_encode] at this

/-- **Every number names a word.** -/
theorem encode_decode (n : ℕ) : encode (decode n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => rw [decode_zero]; rfl
      | (m + 1) =>
          rw [decode]
          by_cases hodd : (m + 1) % 2 = 1
          · rw [if_pos hodd]
            have hlt : m / 2 < m + 1 := by omega
            have hm : encode (decode (m / 2)) = m / 2 := ih _ hlt
            have : encode (Link.p279 :: decode (m / 2)) = 2 * (m / 2) + 1 := by
              rw [show encode (Link.p279 :: decode (m / 2))
                    = 2 * encode (decode (m / 2)) + 1 from rfl, hm]
            rw [this]
            omega
          · rw [if_neg hodd]
            have hlt : (m - 1) / 2 < m + 1 := by omega
            have hm : encode (decode ((m - 1) / 2)) = (m - 1) / 2 := ih _ hlt
            have : encode (Link.p31 :: decode ((m - 1) / 2)) = 2 * ((m - 1) / 2) + 2 := by
              rw [show encode (Link.p31 :: decode ((m - 1) / 2))
                    = 2 * encode (decode ((m - 1) / 2)) + 2 from rfl, hm]
            rw [this]
            omega

/-- **Programs are numbers**: the Gödel numbering is a bijection between the
transformations of the ontology layer and the natural numbers. -/
def equivNat : List Link ≃ ℕ where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-! ### The grading by metaclass level -/

/-- **The degree of a program**: the shift of metaclass level it performs, as an
integer. -/
def degree (w : List Link) : ℤ := (instCount w : ℤ)

@[simp] theorem degree_nil : degree [] = 0 := rfl

/-- The number of `instance of` letters is additive along concatenation. -/
theorem instCount_append (v w : List Link) :
    instCount (v ++ w) = instCount v + instCount w := by
  induction v with
  | nil => simp
  | cons l v ih =>
      cases l with
      | p279 => simpa using ih
      | p31 => simp [ih]; omega

/-- **The degree is a monoid homomorphism** from words under concatenation to the
integers under addition. -/
theorem degree_append (v w : List Link) : degree (v ++ w) = degree v + degree w := by
  simp [degree, instCount_append]

end RelWord

namespace Ontology

variable {I : Type*} {O : Ontology I}

/-- **The degree is the level displacement**: running a program moves the
metaclass level by its degree. -/
theorem level_add_degree {w : List Link} {x y : I}
    (h : PathExpr.Eval O.linkRel (wordExpr w) x y) :
    (O.level y : ℤ) = (O.level x : ℤ) + RelWord.degree w := by
  have := level_of_eval_wordExpr w h
  simp [RelWord.degree, this]

/-- **Closed programs have degree zero**: only the degree-zero part of the
transformation algebra can contain loops. -/
theorem degree_eq_zero_of_closed {w : List Link} {x : I}
    (h : PathExpr.Eval O.linkRel (wordExpr w) x x) : RelWord.degree w = 0 := by
  simp [RelWord.degree, instCount_eq_zero_of_closed h]

end Ontology

/-! ### Composition, and functoriality in the knowledge base -/

namespace KB

variable {kb : KB}

@[simp] theorem wordStep_nil (x : Qid) : kb.wordStep [] x = [x] := rfl

/-- **Concatenation of programs is composition of operators.** -/
theorem wordStep_append (v w : List Link) (x y : Qid) :
    y ∈ kb.wordStep (v ++ w) x ↔ ∃ m, m ∈ kb.wordStep v x ∧ y ∈ kb.wordStep w m := by
  induction v generalizing x with
  | nil =>
      simp only [List.nil_append, wordStep_nil, List.mem_singleton]
      constructor
      · intro h; exact ⟨x, rfl, h⟩
      · rintro ⟨m, rfl, h⟩; exact h
  | cons l v ih =>
      simp only [List.cons_append, wordStep, List.mem_dedup, List.mem_flatMap]
      constructor
      · rintro ⟨u, hu, hy⟩
        obtain ⟨m, hm, hym⟩ := (ih u).1 hy
        exact ⟨m, ⟨u, hu, hm⟩, hym⟩
      · rintro ⟨m, ⟨u, hu, hm⟩, hym⟩
        exact ⟨u, hu, (ih u).2 ⟨m, hm, hym⟩⟩

/-- **A stage that only deletes statements is a morphism of transformation
algebras**: every run of a program in the smaller base is a run of the same
program in the bigger one.  The repair pipeline of the defect report — four
deletions, then the removal of the redundant statements — is such a stage. -/
theorem wordStep_mono {kb' : KB} (hsub : ∀ e ∈ kb'.sub, e ∈ kb.sub)
    (hinst : ∀ e ∈ kb'.inst, e ∈ kb.inst) (w : List Link) (x y : Qid)
    (h : y ∈ kb'.wordStep w x) : y ∈ kb.wordStep w x := by
  induction w generalizing x with
  | nil => simpa using h
  | cons l w ih =>
      simp only [wordStep, List.mem_dedup, List.mem_flatMap] at h ⊢
      obtain ⟨u, hu, hy⟩ := h
      refine ⟨u, ?_, ih u hy⟩
      cases l with
      | p279 => exact mem_supersL.2 (hsub (x, u) (mem_supersL.1 hu))
      | p31 => exact mem_directClassesL.2 (hinst (x, u) (mem_directClassesL.1 hu))

end KB

/-! ### The algebra of relations on a finite carrier -/

namespace RelAlg

variable {α : Type*} [DecidableEq α]

/-- Composition of two finite relations. -/
def comp (R S : Finset (α × α)) : Finset (α × α) :=
  ((R ×ˢ S).filter (fun p => p.1.2 = p.2.1)).image (fun p => (p.1.1, p.2.2))

theorem mem_comp {R S : Finset (α × α)} {a c : α} :
    (a, c) ∈ comp R S ↔ ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S := by
  constructor
  · intro h
    rw [comp, Finset.mem_image] at h
    obtain ⟨⟨⟨a₁, b₁⟩, ⟨b₂, c₂⟩⟩, hp, hpe⟩ := h
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hR, hS⟩, hmid⟩ := hp
    simp only [Prod.mk.injEq] at hpe
    obtain ⟨rfl, rfl⟩ := hpe
    simp only at hmid
    subst hmid
    exact ⟨b₁, hR, hS⟩
  · rintro ⟨b, hR, hS⟩
    rw [comp, Finset.mem_image]
    refine ⟨((a, b), (b, c)), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hR, hS⟩, rfl⟩

/-- The identity relation on a carrier. -/
def idRel (V : Finset α) : Finset (α × α) := V.image (fun a => (a, a))

/-- The `n`-th power of a relation. -/
def pow (V : Finset α) (R : Finset (α × α)) : ℕ → Finset (α × α)
  | 0 => idRel V
  | (n + 1) => comp (pow V R n) R

theorem comp_subset {V : Finset α} {R S : Finset (α × α)} (hR : R ⊆ V ×ˢ V)
    (hS : S ⊆ V ×ˢ V) : comp R S ⊆ V ×ˢ V := by
  intro p hp
  obtain ⟨a, c⟩ := p
  obtain ⟨b, hab, hbc⟩ := mem_comp.1 hp
  have h1 := hR hab
  have h2 := hS hbc
  rw [Finset.mem_product] at h1 h2 ⊢
  exact ⟨h1.1, h2.2⟩

theorem idRel_subset (V : Finset α) : idRel V ⊆ V ×ˢ V := by
  intro p hp
  simp only [idRel, Finset.mem_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  exact Finset.mem_product.2 ⟨ha, ha⟩

theorem pow_subset {V : Finset α} {R : Finset (α × α)} (hR : R ⊆ V ×ˢ V) (n : ℕ) :
    pow V R n ⊆ V ×ˢ V := by
  induction n with
  | zero => exact idRel_subset V
  | succ n ih => exact comp_subset ih hR

/-- **The powers of a relation on a finite carrier are eventually periodic**: the
transformation algebra generated by one program repeats itself. -/
theorem exists_eventually_periodic (V : Finset α) (R : Finset (α × α)) (hR : R ⊆ V ×ˢ V) :
    ∃ i p, 0 < p ∧ ∀ k, i ≤ k → pow V R (k + p) = pow V R k := by
  classical
  set N := ((V ×ˢ V).powerset).card with hN
  have hmaps : ∀ n ∈ Finset.range (N + 1), pow V R n ∈ (V ×ˢ V).powerset := by
    intro n _
    exact Finset.mem_powerset.2 (pow_subset hR n)
  have hcard : ((V ×ˢ V).powerset).card < (Finset.range (N + 1)).card := by
    simp [hN]
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  -- order the two indices
  rcases Nat.lt_or_ge a b with hlt | hge
  · refine ⟨a, b - a, by omega, ?_⟩
    have hstep : pow V R (a + (b - a)) = pow V R a := by
      rw [show a + (b - a) = b by omega]; exact heq.symm
    intro k hk
    induction k with
    | zero =>
        have : a = 0 := by omega
        subst this
        simpa using hstep
    | succ k ih =>
        rcases Nat.lt_or_ge a (k + 1) with hlt' | hge'
        · have hprev := ih (by omega)
          rw [show k + 1 + (b - a) = (k + (b - a)) + 1 by omega, pow, pow, hprev]
        · have : a = k + 1 := by omega
          subst this
          exact hstep
  · have hlt : b < a := by omega
    refine ⟨b, a - b, by omega, ?_⟩
    have hstep : pow V R (b + (a - b)) = pow V R b := by
      rw [show b + (a - b) = a by omega]; exact heq
    intro k hk
    induction k with
    | zero =>
        have : b = 0 := by omega
        subst this
        simpa using hstep
    | succ k ih =>
        rcases Nat.lt_or_ge b (k + 1) with hlt' | hge'
        · have hprev := ih (by omega)
          rw [show k + 1 + (a - b) = (k + (a - b)) + 1 by omega, pow, pow, hprev]
        · have : b = k + 1 := by omega
          subst this
          exact hstep

end RelAlg

end Wikidata
