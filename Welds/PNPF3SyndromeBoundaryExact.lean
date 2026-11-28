import Mathlib
import Welds.PNPSignedCharacterGuardedBlockExact

namespace PNPF3SyndromeBoundary

-- Fixed-length independent ternary coordinates, not Z/(3^r).
abbrev Syndrome (r : Nat) := Fin r → ZMod 3

def Boundary {r : Nat} (U V : Submodule (ZMod 3) (Syndrome r))
    (t s : Syndrome r) : Prop := s ∈ U ∧ t-s ∈ V

theorem boundary_translate {r : Nat} (U V : Submodule (ZMod 3) (Syndrome r))
    (t s₀ d : Syndrome r) (h : Boundary U V t s₀) :
    Boundary U V t (s₀+d) ↔ d ∈ U ∧ d ∈ V := by
  rcases h with ⟨hu,hv⟩
  constructor
  · rintro ⟨hu',hv'⟩
    have a := U.sub_mem hu' hu
    have b := V.sub_mem hv hv'
    constructor
    · convert a using 1 <;> abel
    · convert b using 1 <;> abel
  · rintro ⟨hdU,hdV⟩
    constructor
    · exact U.add_mem hu hdU
    · have a := V.sub_mem hv hdV
      convert a using 1 <;> abel

-- This is an equivalence of original lifts, not just equality of labels.
def Compatible {r : Nat} {A B : Type*} (l : A → Syndrome r)
    (q : B → Syndrome r) (t : Syndrome r) :=
  {p : A × B // l p.1 + q p.2 = t}

def Fibred {r : Nat} {A B : Type*} (l : A → Syndrome r)
    (q : B → Syndrome r) (t : Syndrome r) :=
  Σ s : Syndrome r, {x : A // l x = s} × {y : B // q y = t-s}

def splitEquiv {r : Nat} {A B : Type*} (l : A → Syndrome r)
    (q : B → Syndrome r) (t : Syndrome r) :
    Compatible l q t ≃ Fibred l q t where
  toFun p := ⟨l p.val.1, ⟨p.val.1,rfl⟩, ⟨p.val.2, by rw [← p.property]; abel⟩⟩
  invFun p := ⟨(p.2.1.val,p.2.2.val), by rw [p.2.1.property,p.2.2.property]; abel⟩
  left_inv p := by cases p; rfl
  right_inv p := by
    rcases p with ⟨s,⟨x,hx⟩,⟨y,hy⟩⟩
    subst s
    rfl

-- Boundary labels do not create ternary ambient-volume multiplicity.
-- They partition the actual Boolean source pairs via the above equivalence.
noncomputable def sourceCard {r : Nat} {A B : Type*}
    [Fintype A] [Fintype B] (l : A → Syndrome r)
    (q : B → Syndrome r) (t : Syndrome r) : Nat := by
  classical
  exact Fintype.card (Compatible l q t)

theorem unique_complement {r : Nat} (s u v t : Syndrome r)
    (h : s+u=t) (h' : s+v=t) : u=v := by
  exact add_left_cancel (h.trans h'.symm)

open PNPSignedCharacterTail

def hadd (x y : Hist) : Hist := ⟨x.a+y.a,x.b+y.b,x.c+y.c⟩
def mass (x : Hist) : ℚ := x.a+x.b+x.c

theorem mass_conv (x y : Hist) : mass (conv x y) = mass x * mass y := by
  simp only [mass,conv]; ring

-- Retained head times retained head; the three remaining products
-- are disjoint omitted subsets, with multiplicities intact.
theorem omitted_products (h j p q : Hist) :
    conv (hadd h p) (hadd j q) =
      hadd (conv h j) (hadd (conv h q) (hadd (conv p j) (conv p q))) := by
  cases h; cases j; cases p; cases q
  simp only [hadd,conv]
  congr 1 <;> ring

theorem omitted_mass (h j p q : Hist) :
    mass (hadd (conv h q) (hadd (conv p j) (conv p q))) =
      mass h * mass q + mass j * mass p + mass p * mass q := by
  simp only [hadd,conv,mass]; ring

end PNPF3SyndromeBoundary
