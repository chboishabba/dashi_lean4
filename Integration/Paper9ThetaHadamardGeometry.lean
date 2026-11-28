import Integration.Paper9ActualJSourceJet
import Mathlib

/-! Classical Jacobi four-theta identity, via the D4 Hadamard
coordinate construction. DASHI contribution: original-coordinate
bijections of every norm shell, retaining the signed residual sheet.
SOURCE-WRITTEN, local kernel pending. The all-index shell identity is
not yet the analytic theta/Eisenstein same-object theorem. -/
namespace Integration.Paper9ThetaHadamardGeometry

@[ext] structure Quad where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

def total (x : Quad) : ℤ := x.a+x.b+x.c+x.d
def normSq (x : Quad) : ℤ := x.a^2+x.b^2+x.c^2+x.d^2

def H (x : Quad) : Quad :=
  ⟨x.a+x.b+x.c+x.d, x.a+x.b-x.c-x.d,
   x.a-x.b+x.c-x.d, x.a-x.b-x.c+x.d⟩

def scale (k : ℤ) (x : Quad) : Quad :=
  ⟨k*x.a,k*x.b,k*x.c,k*x.d⟩

def div4 (x : Quad) : Quad :=
  ⟨x.a/4,x.b/4,x.c/4,x.d/4⟩

def flip (x : Quad) : Quad := ⟨-x.a,x.b,x.c,x.d⟩

theorem HH (x : Quad) : H (H x)=scale 4 x := by
  ext <;> simp [H,scale] <;> ring

theorem Hnorm (x : Quad) : normSq (H x)=4*normSq x := by
  unfold normSq H
  ring

theorem Htotal (x : Quad) : total (H x)=4*x.a := by
  unfold total H
  ring

theorem flipFlip (x : Quad) : flip (flip x)=x := by
  ext <;> simp [flip]

theorem flipNorm (x : Quad) : normSq (flip x)=normSq x := by
  unfold normSq flip
  ring

def Odd (x : Quad) : Prop :=
  x.a%2=1 ∧ x.b%2=1 ∧ x.c%2=1 ∧ x.d%2=1

theorem Hodd (x : Quad) (hx : total x%2=1) : Odd (H x) := by
  rcases x with ⟨a,b,c,d⟩
  simp only [total] at hx
  simp only [Odd,H]
  omega

theorem oddFlip (x : Quad) (hx : Odd x) : Odd (flip x) := by
  rcases x with ⟨a,b,c,d⟩
  simp only [Odd,flip] at *
  omega

theorem evenTotal (x : Quad) (hx : Odd x) : total x%2=0 := by
  rcases x with ⟨a,b,c,d⟩
  simp only [Odd] at hx
  simp only [total]
  omega

theorem flipParity (x : Quad) (hx : Odd x) :
    total (flip x)%4 = (total x+2)%4 := by
  rcases x with ⟨a,b,c,d⟩
  simp only [Odd] at hx
  simp only [total,flip]
  omega

theorem HdivExact (x : Quad) (hx : Odd x) (ht : total x%4=0) :
    scale 4 (div4 (H x))=H x := by
  rcases x with ⟨a,b,c,d⟩
  simp only [Odd] at hx
  simp only [total] at ht
  ext <;> simp only [scale,div4,H] <;> omega

theorem Hscale (k : ℤ) (x : Quad) : H (scale k x)=scale k (H x) := by
  cases x
  congr 1 <;> simp [H,scale] <;> ring

theorem scale4Injective : Function.Injective (scale 4) := by
  intro x y h
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h'⟩
  simp only [scale,Quad.mk.injEq] at h
  ext <;> omega

theorem reopen (y : Quad) (hy : Odd y) (hs : total y%4=0) :
    H (div4 (H y))=y := by
  apply scale4Injective
  rw [← Hscale, HdivExact y hy hs, HH]

theorem decodeEncode (x : Quad) : div4 (H (H x))=x := by
  rw [HH]
  ext <;> simp [div4,scale] <;> omega

theorem reopenOdd (y : Quad) (hy : Odd y) (hs : total y%4=0) :
    total (div4 (H y))%2=1 := by
  have h := congrArg Quad.a (reopen y hy hs)
  change total (div4 (H y))=y.a at h
  rw [h]
  exact hy.1

theorem reopenNorm (y : Quad) (hy : Odd y) (hs : total y%4=0)
    (n : ℕ) (hn : normSq y=4*(n:ℤ)) :
    normSq (div4 (H y))=(n:ℤ) := by
  have h := Hnorm (div4 (H y))
  rw [reopen y hy hs,hn] at h
  omega

-- Every grade, including zero. No abstract equal-cardinality choice.
def IntegerOddShell (n : ℕ) :=
  {x : Quad // normSq x=(n:ℤ) ∧ total x%2=1}

def HalfEvenShell (n : ℕ) :=
  {y : Quad // normSq y=4*(n:ℤ) ∧ Odd y ∧ total y%4=0}

def HalfOddShell (n : ℕ) :=
  {y : Quad // normSq y=4*(n:ℤ) ∧ Odd y ∧ total y%4=2}

def HalfShell (n : ℕ) :=
  {y : Quad // normSq y=4*(n:ℤ) ∧ Odd y}

def integerHalf (n : ℕ) : IntegerOddShell n ≃ HalfEvenShell n where
  toFun x := ⟨H x.val,by rw [Hnorm,x.property.1],
    Hodd x.val x.property.2,by rw [Htotal]; omega⟩
  invFun y := ⟨div4 (H y.val),
    reopenNorm y.val y.property.2.1 y.property.2.2 n y.property.1,
    reopenOdd y.val y.property.2.1 y.property.2.2⟩
  left_inv x := Subtype.ext (decodeEncode x.val)
  right_inv y := Subtype.ext (reopen y.val y.property.2.1 y.property.2.2)

def halfFlip (n : ℕ) : HalfEvenShell n ≃ HalfOddShell n where
  toFun y := ⟨flip y.val,by rw [flipNorm,y.property.1],
    oddFlip y.val y.property.2.1,by rw [flipParity _ y.property.2.1]; omega⟩
  invFun y := ⟨flip y.val,by rw [flipNorm,y.property.1],
    oddFlip y.val y.property.2.1,by rw [flipParity _ y.property.2.1]; omega⟩
  left_inv y := Subtype.ext (flipFlip y.val)
  right_inv y := Subtype.ext (flipFlip y.val)

def splitHalf (n : ℕ) : HalfShell n ≃ HalfEvenShell n ⊕ HalfOddShell n where
  toFun y := if h : total y.val%4=0 then
    Sum.inl ⟨y.val,y.property.1,y.property.2,h⟩
    else Sum.inr ⟨y.val,y.property.1,y.property.2,by
      have he := evenTotal y.val y.property.2
      omega⟩
  invFun y := match y with
    | .inl x => ⟨x.val,x.property.1,x.property.2.1⟩
    | .inr x => ⟨x.val,x.property.1,x.property.2.1⟩
  left_inv y := by
    split <;> rfl
  right_inv y := by
    cases y with
    | inl x => simp [x.property.2.2]
    | inr x => simp [x.property.2.2]

-- Half-sheet reconstruction on the actual indexed norm fibres.
-- The two equal multiplicities are not identified as one sheet.
def halfTwoCopies (n : ℕ) : HalfShell n ≃ IntegerOddShell n ⊕ IntegerOddShell n :=
  (splitHalf n).trans (Equiv.sumCongr (integerHalf n).symm
    ((halfFlip n).symm.trans (integerHalf n).symm))

-- Explicit independent norm parity law used by theta4.
theorem squareParity (a : ℤ) : a^2%2=a%2 := by
  have h : a=2*(a/2)+a%2 := by omega
  have hm : a%2=0 ∨ a%2=1 := by omega
  rcases hm with h0|h1
  · have he : a^2=2*(2*(a/2)^2) := by
      calc
        a^2 = (2*(a/2)+a%2)^2 := congrArg (fun z : ℤ => z^2) h
        _ = _ := by rw [h0]; ring
    omega
  · have he : a^2=2*(2*(a/2)^2+2*(a/2))+1 := by
      calc
        a^2 = (2*(a/2)+a%2)^2 := congrArg (fun z : ℤ => z^2) h
        _ = _ := by rw [h1]; ring
    omega

theorem normParity (x : Quad) : normSq x%2=total x%2 := by
  have a := squareParity x.a
  have b := squareParity x.b
  have c := squareParity x.c
  have d := squareParity x.d
  unfold normSq total
  omega

-- The actual count-level Jacobi cancellation is a corollary of the
-- reversible map, not an imported count equality. These bounded norm
-- fibres are finite; the Nat.card equation is also meaningful without
-- choosing an enumeration for them.
theorem halfCard (n : ℕ) :
    Nat.card (HalfShell n) =
      Nat.card (IntegerOddShell n ⊕ IntegerOddShell n) :=
  Nat.card_congr (halfTwoCopies n)

-- A coordinate bound follows from a squared norm budget, including
-- n=0. This makes the shell equivalences genuinely finite.
theorem coordBound (a : ℤ) (n : ℕ) (ha : a^2≤(n:ℤ)) :
    -(n:ℤ)≤a ∧ a≤(n:ℤ) := by
  have hn : (0:ℤ)≤(n:ℤ) := by positivity
  constructor
  · by_contra h
    have h1 : a≤ -1 := by omega
    have h2 := mul_nonneg (show 0≤-a by omega) (show 0≤-a-1 by omega)
    nlinarith
  · by_contra h
    have h1 : 1≤a := by omega
    have h2 := mul_nonneg (show 0≤a by omega) (show 0≤a-1 by omega)
    nlinarith

def NormShell (n : ℕ) := {x : Quad // normSq x=(n:ℤ)}

def coordFin (a : ℤ) (n : ℕ) (ha : -(n:ℤ)≤a ∧ a≤(n:ℤ)) :
    Fin (2*n+1) :=
  ⟨(a+(n:ℤ)).toNat,by omega⟩

theorem coordFinInjective (n : ℕ) (a b : ℤ)
    (ha : -(n:ℤ)≤a ∧ a≤(n:ℤ)) (hb : -(n:ℤ)≤b ∧ b≤(n:ℤ))
    (h : coordFin a n ha=coordFin b n hb) : a=b := by
  have h' := congrArg Fin.val h
  change (a+(n:ℤ)).toNat=(b+(n:ℤ)).toNat at h'
  omega

def shellCode (n : ℕ) (x : NormShell n) :
    Fin (2*n+1) × Fin (2*n+1) × Fin (2*n+1) × Fin (2*n+1) :=
  have h := x.property
  ⟨coordFin x.val.a n (coordBound _ _ (by unfold normSq at h; nlinarith [sq_nonneg x.val.b,sq_nonneg x.val.c,sq_nonneg x.val.d])),
   coordFin x.val.b n (coordBound _ _ (by unfold normSq at h; nlinarith [sq_nonneg x.val.a,sq_nonneg x.val.c,sq_nonneg x.val.d])),
   coordFin x.val.c n (coordBound _ _ (by unfold normSq at h; nlinarith [sq_nonneg x.val.a,sq_nonneg x.val.b,sq_nonneg x.val.d])),
   coordFin x.val.d n (coordBound _ _ (by unfold normSq at h; nlinarith [sq_nonneg x.val.a,sq_nonneg x.val.b,sq_nonneg x.val.c]))⟩

theorem shellCodeInjective (n : ℕ) : Function.Injective (shellCode n) := by
  intro x y h
  apply Subtype.ext
  apply Quad.ext
  · exact coordFinInjective n _ _ _ _ (congrArg Prod.fst h)
  · exact coordFinInjective n _ _ _ _ (congrArg (fun z => z.2.1) h)
  · exact coordFinInjective n _ _ _ _ (congrArg (fun z => z.2.2.1) h)
  · exact coordFinInjective n _ _ _ _ (congrArg (fun z => z.2.2.2) h)

instance (n : ℕ) : Finite (NormShell n) :=
  Finite.of_injective (shellCode n) (shellCodeInjective n)

instance (n : ℕ) : Finite (IntegerOddShell n) :=
  Finite.of_injective (fun x : IntegerOddShell n => (⟨x.val,x.property.1⟩ : NormShell n))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

instance (n : ℕ) : Finite (HalfShell n) :=
  Finite.of_injective (fun x : HalfShell n => (⟨x.val,by simpa using x.property.1⟩ : NormShell (4*n)))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h))

-- The actual all-index coefficient is signed by norm parity.
-- Even grade contributes zero to B-C; odd grade contributes twice.
def Bcoeff (n : ℕ) : ℤ := Nat.card (NormShell n)
def Ccoeff (n : ℕ) : ℤ := if n%2=0 then Bcoeff n else -Bcoeff n
def Acoeff (n : ℕ) : ℤ := Nat.card (HalfShell n)

theorem halfCardTwice (n : ℕ) :
    Nat.card (HalfShell n)=2*Nat.card (IntegerOddShell n) := by
  rw [halfCard, Nat.card_sum]
  omega

def oddShellFull (n : ℕ) (hn : n%2=1) : IntegerOddShell n ≃ NormShell n where
  toFun x := ⟨x.val,x.property.1⟩
  invFun x := ⟨x.val,x.property,by
    have h := normParity x.val
    rw [x.property] at h
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem oddShellEmpty (n : ℕ) (hn : n%2=0) :
    IsEmpty (IntegerOddShell n) := ⟨fun x => by
  have h := normParity x.val
  rw [x.property.1,x.property.2] at h
  omega⟩

theorem jacobiShell (n : ℕ) : Bcoeff n=Acoeff n+Ccoeff n := by
  by_cases h : n%2=0
  · letI := oddShellEmpty n h
    have ho : Nat.card (IntegerOddShell n)=0 := Nat.card_eq_zero_of_isEmpty
    simp [Bcoeff,Ccoeff,Acoeff,h,halfCardTwice,ho]
  · have hn : n%2=1 := by omega
    have ho := Nat.card_congr (oddShellFull n hn)
    simp [Bcoeff,Ccoeff,Acoeff,h,halfCardTwice,ho]
    ring

-- Shared polynomial invariants in any commutative ring.
section Algebra
variable {S : Type*} [CommRing S]
def Q (a b : S) := a^2-a*b+b^2
def V (a b : S) := a*b*(b-a)
def W (a b : S) := (a+b)*(2*a-b)*(a-2*b)

theorem invariantDiscriminant (a b : S) :
    4*(Q a b)^3 = (W a b)^2+27*(V a b)^2 := by
  unfold Q W V
  ring

theorem halfSheet (a b : S) :
    Q (-a) (b-a)=Q a b ∧ W (-a) (b-a)=W a b ∧
      V (-a) (b-a)= -V a b := by
  unfold Q W V
  constructor
  · ring
  constructor <;> ring

theorem thetaPolynomials (a b c : S) (h : b=a+c) :
    a^2+b^2+c^2=2*Q a b ∧ (a+b)*(b+c)*(c-a)=W a b := by
  subst b
  unfold Q W
  constructor <;> ring
end Algebra

#print axioms integerHalf
#print axioms halfTwoCopies
#print axioms jacobiShell
#print axioms invariantDiscriminant
end Integration.Paper9ThetaHadamardGeometry
