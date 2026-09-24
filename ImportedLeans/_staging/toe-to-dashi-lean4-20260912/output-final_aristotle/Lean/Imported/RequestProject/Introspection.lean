import Mathlib
import RequestProject.Frobenius
import RequestProject.FrobeniusOrbit
import RequestProject.FrobeniusTrace
import RequestProject.RetractiveCore
import RequestProject.CenterRetraction

/-!
# Introspection as the projection of the trace, and the reception history of a reading

This file adds a layer of vocabulary on top of the Frobenius/trace theory of
`RequestProject.FrobeniusTrace`, and proves the statements that make that vocabulary
coherent.

Fix a finite field `K` with `p ^ n` elements.  The `k`-th **viewer** reads an element `x`
through the `k`-th Frobenius iterate,

`reading p k x = x ^ (p ^ k)`,

and the whole sequence of successive readings

`history p x = fun k => x ^ (p ^ k)`

is the *Rezeptionsgeschichte* (reception history) of `x`: what each viewer in turn makes of
it.  The history is periodic with period `n` (`history_add_card`), it determines `x`
(`history_injective`, its `0`-th entry being `x` itself), and its set of values is exactly the
Frobenius orbit (`range_history`).  It is *constant* — all viewers agree outright — precisely
for the elements of the prime subfield `𝔽_p` (`history_const_iff`).

The **reaction to the reading** aggregated over all viewers is the trace
`frobTrace p n x = ∑ k < n, history p x k`, and **introspection** is its projection:

`introspect p n x = (n : K)⁻¹ * frobTrace p n x`.

Main results.

* `frobTrace_reading`, `introspect_reading` : *every viewer's reading provokes the same
  reaction*: the trace, and hence the introspection, of `history p x k` is that of `x`.  The
  reception history is invisible to the trace.
* `history_frobTrace`, `history_introspect` : *the reflection of a reaction is constant*: the
  reception history of a trace, or of an introspection, is a constant sequence — all viewers
  see it identically.
* `introspect_idempotent`, `range_introspect`, `introspect_eq_self_iff` : when `p ∤ n`,
  introspection is an **idempotent additive projection of `K` onto `𝔽_p`** whose image, and
  equally whose fixed-point set, is exactly `𝔽_p`; by `history_const_iff` its fixed points are
  exactly the elements with a constant reception history.
* `introspection_theorem` packages all of this into one statement.
* `GF8` : the instantiation at the field with `2 ^ 3 = 8` elements, where `p ∤ n` holds.
* `Group.centerRetraction_introspection_theorem` : the same five clauses hold verbatim for a
  retraction onto the center of a group, with the viewers now the conjugations `x ↦ g x g⁻¹`:
  the reaction is the same for every viewer, its reception history is constant, and the
  retraction is an idempotent whose image and fixed-point set are the center — the elements
  with constant reception history.

The idempotence is recorded in the vocabulary of `RetractiveCore.IsIdempotent`, so that
`RetractiveCore.IsIdempotent.range_eq_fixedPoints` applies verbatim: introspection is a
retraction onto its image, exactly as the center retractions of the group half of the
project are retractions onto the center.
-/

open Finset FrobeniusPrimeSubfield

namespace Rezeption

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-! ### Viewers and the reception history -/

variable (p) in
/-- The reading of `x` by the `k`-th viewer: the `k`-th Frobenius iterate `x ↦ x ^ (p ^ k)`. -/
def reading (k : ℕ) (x : K) : K := x ^ p ^ k

variable (p) in
/-- The *Rezeptionsgeschichte* of `x`: the sequence of readings of `x` by the successive
viewers, `k ↦ x ^ (p ^ k)`. -/
def history (x : K) : ℕ → K := fun k => reading p k x

omit hp [CharP K p] in
@[simp] theorem history_apply (x : K) (k : ℕ) : history p x k = x ^ p ^ k := rfl

omit hp [CharP K p] in
@[simp] theorem history_zero (x : K) : history p x 0 = x := by
  simp [history, reading]

omit hp [CharP K p] in
/-- Each viewer reads the previous viewer's reading through the Frobenius. -/
theorem history_succ (x : K) (k : ℕ) : history p x (k + 1) = (history p x k) ^ p := by
  simp [history, reading, ← pow_mul, pow_succ]

omit hp [CharP K p] in
/-- The values of the reception history are exactly the Frobenius orbit. -/
theorem range_history (x : K) : Set.range (history p x) = frobOrbit p x := rfl

omit hp [CharP K p] in
/-- A reception history determines the element it is the history of: the first viewer already
reads `x` itself. -/
theorem history_injective : Function.Injective (history p : K → ℕ → K) := by
  intro x y h
  simpa using congrFun h 0

/-- **All viewers agree on `x` exactly when `x` lies in the prime subfield**: the reception
history is constant precisely on `𝔽_p`. -/
theorem history_const_iff (x : K) :
    (∀ k, history p x k = x) ↔ x ∈ Set.range (primeSubfieldHom K p) :=
  forall_pow_pow_char_eq_self_iff x

/-! ### Introspection: the projection of the trace -/

variable (p) in
/-- **Introspection**: the projection of the trace, i.e. the normalized reaction of all `n`
viewers to `x`, `x ↦ (n : K)⁻¹ * ∑ k < n, x ^ (p ^ k)`. -/
def introspect (n : ℕ) (x : K) : K := (n : K)⁻¹ * frobTrace p n x

omit hp [CharP K p] in
theorem introspect_def (n : ℕ) (x : K) :
    introspect p n x = (n : K)⁻¹ * frobTrace p n x := rfl

omit hp [CharP K p] in
/-- Introspection is literally the projection of the aggregated reception history. -/
theorem introspect_eq_projection_of_history (n : ℕ) (x : K) :
    introspect p n x = (n : K)⁻¹ * ∑ k ∈ range n, history p x k := rfl

theorem introspect_add (n : ℕ) (x y : K) :
    introspect p n (x + y) = introspect p n x + introspect p n y := by
  simp [introspect, frobTrace_add, mul_add]

section Finite

variable [Fintype K] {n : ℕ}

variable (hK : Nat.card K = p ^ n)
include hK

omit hp [CharP K p] in
/-- The reception history is periodic with period `n`: after `n` viewers the readings begin
again. -/
theorem history_add_card (x : K) (k : ℕ) : history p x (k + n) = history p x k := by
  have h : x ^ p ^ (k + n) = (x ^ p ^ n) ^ p ^ k := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  simp only [history_apply, h, pow_card_pow_eq_self hK x]

/-- The trace does not see the Frobenius: `tr (x ^ p) = tr x`. -/
theorem frobTrace_pow_char_arg (x : K) : frobTrace p n (x ^ p) = frobTrace p n x := by
  have h : frobTrace p n (x ^ p) = (frobTrace p n x) ^ p := by
    rw [frobTrace, frobTrace, FrobeniusPrimeSubfield.sum_pow_char]
    exact Finset.sum_congr rfl fun k _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h, frobTrace_pow_char hK x]

/-- **Every viewer provokes the same reaction**: the trace of the `k`-th reading of `x` is the
trace of `x`. -/
theorem frobTrace_reading (x : K) (k : ℕ) :
    frobTrace p n (history p x k) = frobTrace p n x := by
  induction k with
  | zero => simp
  | succ k ih => rw [history_succ, frobTrace_pow_char_arg hK, ih]

/-- **The reflection of a reaction is constant**: all viewers read the trace identically. -/
theorem history_frobTrace (x : K) (k : ℕ) :
    history p (frobTrace p n x) k = frobTrace p n x :=
  pow_pow_char_eq_self (frobTrace_pow_char hK x) k

theorem introspect_mem_primeSubfield (x : K) :
    introspect p n x ∈ Set.range (primeSubfieldHom K p) := by
  have hninv : ((n : K))⁻¹ ∈ Set.range (primeSubfieldHom K p) := by
    have hnF : (n : K) ∈ fixedSubfield K p 1 := by
      rw [mem_fixedSubfield, pow_one, ← map_natCast (primeSubfieldHom K p) n, ← map_pow,
        ZMod.pow_card]
    have := inv_mem hnF
    rwa [← SetLike.mem_coe, fixedSubfield_one] at this
  obtain ⟨u, hu⟩ := hninv
  obtain ⟨v, hv⟩ := frobTrace_mem_primeSubfield hK x
  exact ⟨u * v, by rw [map_mul, hu, hv]; rfl⟩

/-- The reception history of an introspection is constant. -/
theorem history_introspect (x : K) (k : ℕ) :
    history p (introspect p n x) k = introspect p n x := by
  refine (history_const_iff _).2 (introspect_mem_primeSubfield hK x) k

/-- Every viewer's reading has the same introspection. -/
theorem introspect_reading (x : K) (k : ℕ) :
    introspect p n (history p x k) = introspect p n x := by
  rw [introspect, introspect, frobTrace_reading hK]

variable (hpn : ¬ p ∣ n)
include hpn

omit hp [Fintype K] hK in
theorem cast_card_ne_zero : (n : K) ≠ 0 := fun h => hpn ((CharP.cast_eq_zero_iff K p n).1 h)

omit [Fintype K] hK in
/-- Introspection fixes the prime subfield pointwise. -/
theorem introspect_of_mem_primeSubfield {a : K} (ha : a ∈ Set.range (primeSubfieldHom K p)) :
    introspect p n a = a := by
  have hpa : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ha
  rw [introspect, frobTrace_of_pow_char_eq_self hpa, ← mul_assoc,
    inv_mul_cancel₀ (cast_card_ne_zero (K := K) hpn), one_mul]

/-- **Introspection is a projection**: it is idempotent. -/
theorem introspect_idempotent : RetractiveCore.IsIdempotent (introspect p n : K → K) :=
  fun x => introspect_of_mem_primeSubfield hpn (introspect_mem_primeSubfield hK x)

/-- **The image of introspection is exactly the prime subfield `𝔽_p`.** -/
theorem range_introspect :
    Set.range (introspect p n : K → K) = Set.range (primeSubfieldHom K p) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact introspect_mem_primeSubfield hK x
  · intro a ha
    exact ⟨a, introspect_of_mem_primeSubfield hpn ha⟩

/-- **The fixed points of introspection are exactly the prime subfield**, equivalently exactly
the elements with a constant reception history. -/
theorem introspect_eq_self_iff (x : K) :
    introspect p n x = x ↔ ∀ k, history p x k = x := by
  rw [history_const_iff]
  refine ⟨fun h => h ▸ introspect_mem_primeSubfield hK x, fun h =>
    introspect_of_mem_primeSubfield hpn h⟩

/-- **The introspection theorem.**  For a finite field with `p ^ n` elements and `p ∤ n`:

1. introspection is the projection of the trace, i.e. of the aggregated reception history;
2. it is additive;
3. the reaction is the same for every viewer's reading;
4. the reflection of a reaction is constant: all viewers read an introspection identically;
5. introspection is idempotent, with image exactly `𝔽_p`;
6. its fixed points are exactly the elements whose reception history is constant. -/
theorem introspection_theorem :
    (∀ x : K, introspect p n x = (n : K)⁻¹ * ∑ k ∈ range n, history p x k) ∧
      (∀ x y : K, introspect p n (x + y) = introspect p n x + introspect p n y) ∧
      (∀ (x : K) (k : ℕ), introspect p n (history p x k) = introspect p n x) ∧
      (∀ (x : K) (k : ℕ), history p (introspect p n x) k = introspect p n x) ∧
      RetractiveCore.IsIdempotent (introspect p n : K → K) ∧
      Set.range (introspect p n : K → K) = Set.range (primeSubfieldHom K p) ∧
      (∀ x : K, introspect p n x = x ↔ ∀ k, history p x k = x) :=
  ⟨fun _ => rfl, introspect_add n, introspect_reading hK, history_introspect hK,
    introspect_idempotent hK hpn, range_introspect hK hpn, introspect_eq_self_iff hK hpn⟩

end Finite

/-! ### An instance: the field with eight elements -/

/-- The field with `2 ^ 3 = 8` elements: here `p = 2` does not divide `n = 3`, so introspection
is a genuine projection onto `𝔽₂`. -/
abbrev GF8 := GaloisField 2 3

noncomputable instance : Fintype GF8 := Fintype.ofFinite _

theorem card_GF8 : Nat.card GF8 = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)

/-- Introspection on `GF(8)` is the projection `x ↦ 3⁻¹ (x + x² + x⁴)` of the trace, and it is
an idempotent additive projection of `GF(8)` onto `𝔽₂`, invariant under every viewer. -/
theorem GF8.introspection_theorem :
    (∀ x y : GF8, introspect 2 3 (x + y) = introspect 2 3 x + introspect 2 3 y) ∧
      (∀ (x : GF8) (k : ℕ), introspect 2 3 (history 2 x k) = introspect 2 3 x) ∧
      RetractiveCore.IsIdempotent (introspect 2 3 : GF8 → GF8) ∧
      Set.range (introspect 2 3 : GF8 → GF8) = Set.range (primeSubfieldHom GF8 2) := by
  obtain ⟨-, h2, h3, -, h5, h6, -⟩ :=
    Rezeption.introspection_theorem (K := GF8) (p := 2) (n := 3) card_GF8 (by norm_num)
  exact ⟨h2, h3, h5, h6⟩

/-! ### The group-theoretic mirror: conjugation viewers and the center retraction

The same three clauses — invariance of the reaction under every viewer, constancy of the
reception history of a reaction, and idempotence with fixed-point set the target — hold
verbatim for a retraction onto the center, with the viewers now the conjugations `x ↦ g x g⁻¹`
instead of the Frobenius iterates.
-/

namespace Group

variable {G : Type*} [Group G]

/-- The reading of `x` by the viewer `g`: the conjugate `g x g⁻¹`. -/
def conjReading (g x : G) : G := g * x * g⁻¹

/-- The reception history of `x` under the conjugation viewers. -/
def conjHistory (x : G) : G → G := fun g => conjReading g x

@[simp] theorem conjHistory_apply (x g : G) : conjHistory x g = g * x * g⁻¹ := rfl

/-- The history is constant exactly on the center. -/
theorem conjHistory_const_iff (x : G) :
    (∀ g, conjHistory x g = x) ↔ x ∈ Subgroup.center G := by
  simp only [conjHistory_apply, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg := h g
    rwa [mul_inv_eq_iff_eq_mul] at hg
  · intro h g
    rw [h g, mul_assoc, mul_inv_cancel, mul_one]

variable {r : G →* Subgroup.center G} (hr : ∀ z : Subgroup.center G, r z = z)

/-- **Every viewer provokes the same reaction**: a retraction onto the center is invariant
under conjugation. -/
theorem centerRetraction_conjReading (x g : G) : r (conjHistory x g) = r x := by
  simp only [conjHistory_apply, map_mul, map_inv]
  rw [mul_comm (r g) (r x), mul_assoc, mul_inv_cancel, mul_one]

/-- **The reflection of a reaction is constant**: all viewers read the value of the retraction
identically. -/
theorem conjHistory_centerRetraction (x g : G) :
    conjHistory ((r x : G)) g = (r x : G) :=
  (conjHistory_const_iff _).2 (r x).2 g

include hr

/-- The retraction, viewed as a self-map of `G`, is idempotent. -/
theorem centerRetraction_isIdempotent :
    RetractiveCore.IsIdempotent (fun x : G => (r x : G)) :=
  fun x => congrArg Subtype.val (hr (r x))

/-- Its image is exactly the center. -/
theorem range_centerRetraction :
    Set.range (fun x : G => (r x : G)) = (Subgroup.center G : Set G) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact (r x).2
  · intro z hz
    exact ⟨z, congrArg Subtype.val (hr ⟨z, hz⟩)⟩

/-- Its fixed points are exactly the elements with a constant reception history. -/
theorem centerRetraction_eq_self_iff (x : G) :
    (r x : G) = x ↔ ∀ g, conjHistory x g = x := by
  rw [conjHistory_const_iff]
  exact ⟨fun h => h ▸ (r x).2, fun h => congrArg Subtype.val (hr ⟨x, h⟩)⟩

omit hr in
/-- **The introspection theorem, group form.**  If `G` retracts onto its center, the
retraction is a self-map `f` of `G` which: gives the same reaction to every viewer's reading
`g x g⁻¹`; has constant reception history; is idempotent with image exactly the center; and
fixes exactly the elements with constant reception history — the same five clauses as
`Rezeption.introspection_theorem`, with conjugations in place of Frobenius iterates. -/
theorem centerRetraction_introspection_theorem (h : HasCenterRetraction G) :
    ∃ f : G → G,
      (∀ (x g : G), f (conjHistory x g) = f x) ∧
      (∀ (x g : G), conjHistory (f x) g = f x) ∧
      RetractiveCore.IsIdempotent f ∧
      Set.range f = (Subgroup.center G : Set G) ∧
      (∀ x : G, f x = x ↔ ∀ g, conjHistory x g = x) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨fun x => (r x : G), fun x g => congrArg Subtype.val (centerRetraction_conjReading x g),
    fun x g => conjHistory_centerRetraction x g, centerRetraction_isIdempotent hr,
    range_centerRetraction hr, centerRetraction_eq_self_iff hr⟩

end Group

end Rezeption
