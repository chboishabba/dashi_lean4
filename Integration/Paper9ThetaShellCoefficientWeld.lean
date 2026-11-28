import Integration.Paper9ThetaHadamardGeometry

/-! SOURCE-WRITTEN, kernel pending. Exact graded Cartesian fibre
decomposition of the original D4 shells. Classical theta-series
combinatorics; DASHI contribution is the explicit indexed inverse and
attachment to the literal finite square/triangular coefficient scans.
No modularity or analytic identity theorem is assumed. -/
namespace Integration.Paper9ThetaShellCoefficientWeld
open Integration.Paper9ThetaHadamardGeometry
open scoped BigOperators
noncomputable section

def Fibre {α : Type*} (g : α → ℕ) (n : ℕ) := {x : α // g x = n}

def gradePair {α β : Type*} (g : α → ℕ) (h : β → ℕ) (x : α × β) :=
  g x.1 + h x.2

-- Explicit grades are retained by the inverse; n-i is used only on
-- the certified finite grade i <= n.
def pairFibre {α β : Type*} (g : α → ℕ) (h : β → ℕ) (n : ℕ) :
    Fibre (gradePair g h) n ≃
      Σ i : Fin (n+1), Fibre g i.val × Fibre h (n-i.val) where
  toFun x :=
    have he := x.property
    ⟨⟨g x.val.1,by unfold gradePair at he; omega⟩,
      ⟨x.val.1,rfl⟩,⟨x.val.2,by unfold gradePair at he; omega⟩⟩
  invFun x := ⟨(x.2.1.val,x.2.2.val),by
    unfold gradePair
    rw [x.2.1.property,x.2.2.property]
    have hi := x.1.isLt
    omega⟩
  left_inv x := Subtype.ext rfl
  right_inv x := by
    rcases x with ⟨i,u,v⟩
    have he := u.property
    cases i with
    | mk i hi =>
      dsimp at he
      dsimp
      cases he
      rfl

instance pairFinite {α β : Type*} (g : α → ℕ) (h : β → ℕ)
    [∀ n, Finite (Fibre g n)] [∀ n, Finite (Fibre h n)] (n : ℕ) :
    Finite (Fibre (gradePair g h) n) :=
  Finite.of_injective (pairFibre g h n) (pairFibre g h n).injective

def row (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i : Fin (n+1), f i.val * g (n-i.val)

def fourth (f : ℕ → ℕ) : ℕ → ℕ := row (row f f) (row f f)

theorem pairCard {α β : Type*} (g : α → ℕ) (h : β → ℕ)
    [∀ n, Finite (Fibre g n)] [∀ n, Finite (Fibre h n)] (n : ℕ) :
    Nat.card (Fibre (gradePair g h) n) =
      row (fun i => Nat.card (Fibre g i)) (fun i => Nat.card (Fibre h i)) n := by
  classical
  letI (i : ℕ) : Fintype (Fibre g i) := Fintype.ofFinite _
  letI (i : ℕ) : Fintype (Fibre h i) := Fintype.ofFinite _
  rw [Nat.card_congr (pairFibre g h n), Nat.card_eq_fintype_card, Fintype.card_sigma]
  unfold row
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

def fourGrade {α : Type*} (g : α → ℕ) := gradePair (gradePair g g) (gradePair g g)

theorem fourCard {α : Type*} (g : α → ℕ) [∀ n, Finite (Fibre g n)] (n : ℕ) :
    Nat.card (Fibre (fourGrade g) n) = fourth (fun i => Nat.card (Fibre g i)) n := by
  unfold fourGrade fourth
  rw [pairCard]
  unfold row
  apply Finset.sum_congr rfl
  intro i _
  rw [pairCard, pairCard]

-- Literal scan, including index zero, agrees with the Agda count
-- recurrence. No bounded-prefix equality is promoted to all n.
def scan (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => if f 0=n then 1 else 0
  | k+1 => (if f (k+1)=n then 1 else 0)+scan f n k

theorem scanCard (f : ℕ → ℕ) (n k : ℕ) :
    ((Finset.range (k+1)).filter (fun j => f j=n)).card = scan f n k := by
  classical
  induction k with
  | zero =>
    by_cases h : f 0=n <;> simp [scan,h]
  | succ k ih =>
    rw [Finset.range_succ]
    by_cases h : f (k+1)=n
    · simp [Finset.filter_insert,h,Finset.card_insert_of_notMem,ih,scan,add_comm]
    · simp [Finset.filter_insert,h,ih,scan]

def boundedFibre (f : ℕ → ℕ) (n : ℕ) (bound : ∀ j, f j=n → j≤n) :
    Fibre f n ≃ ↥((Finset.range (n+1)).filter (fun j => f j=n)) where
  toFun x := ⟨x.val, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by have h := bound x.val x.property; omega),x.property⟩⟩
  invFun x := ⟨x.val,(Finset.mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundedCard (f : ℕ → ℕ) (n : ℕ) (bound : ∀ j, f j=n → j≤n) :
    Nat.card (Fibre f n)=scan f n n := by
  classical
  rw [Nat.card_congr (boundedFibre f n bound), Nat.card_eq_fintype_card, Fintype.card_coe,scanCard]

def sq (j : ℕ) := j*j
def tri (j : ℕ) := j*(j+1)

theorem sqBound (j n : ℕ) (h : sq j=n) : j≤n := by
  cases j with
  | zero => omega
  | succ j =>
    unfold sq at h
    have hm := Nat.mul_le_mul_left (j+1) (show 1≤j+1 by omega)
    omega

theorem triBound (j n : ℕ) (h : tri j=n) : j≤n := by
  unfold tri at h
  have hm := Nat.mul_le_mul_left j (show 1≤j+1 by omega)
  omega

instance sqFinite (n : ℕ) : Finite (Fibre sq n) :=
  Finite.of_injective (boundedFibre sq n (fun j h => sqBound j n h)) (boundedFibre sq n _).injective

instance triFinite (n : ℕ) : Finite (Fibre tri n) :=
  Finite.of_injective (boundedFibre tri n (fun j h => triBound j n h)) (boundedFibre tri n _).injective

def intGrade : ℤ → ℕ
  | .ofNat k => sq k
  | .negSucc k => sq (k+1)

theorem intGradeRead (z : ℤ) : (intGrade z : ℤ)=z^2 := by
  cases z <;> simp [intGrade,sq] <;> push_cast <;> ring

instance intFinite (n : ℕ) : Finite (Fibre intGrade n) :=
  Finite.of_injective (fun x : Fibre intGrade n =>
    (⟨⟨x.val,0,0,0⟩,by
      have h := intGradeRead x.val
      rw [x.property] at h
      simpa [normSq] using h.symm⟩ : NormShell n))
    (fun _ _ h => Subtype.ext (congrArg (fun z : NormShell n => z.val.a) h))

-- For n>0, each magnitude occurs once in each polarity. Zero instead
-- has exactly one preimage and is never doubled.
def signedSquare (n : ℕ) (hn : 0<n) : Fibre intGrade n ≃ Fibre sq n × Bool where
  toFun x := match hx : x.val with
    | .ofNat k => (⟨k,by simpa [hx,intGrade] using x.property⟩,false)
    | .negSucc k => (⟨k+1,by simpa [hx,intGrade] using x.property⟩,true)
  invFun x := match x.2 with
    | false => ⟨Int.ofNat x.1.val,x.1.property⟩
    | true => ⟨Int.negSucc (x.1.val-1),by
      have hp : x.1.val≠0 := by
        intro h
        have he := x.1.property
        rw [h] at he
        simp [sq] at he
        omega
      change sq (x.1.val-1+1)=n
      rw [show x.1.val-1+1=x.1.val by omega]
      exact x.1.property⟩
  left_inv x := by
    rcases x with ⟨z,hz⟩
    cases z <;> apply Subtype.ext <;> simp
  right_inv x := by
    rcases x with ⟨⟨k,hk⟩,b⟩
    cases k with
    | zero => simp [sq] at hk; omega
    | succ k => cases b <;> rfl

def intZero : Fibre intGrade 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0,rfl⟩
  left_inv x := by
    apply Subtype.ext
    have h := intGradeRead x.val
    rw [x.property] at h
    have he : x.val=0 := by nlinarith
    exact he.symm
  right_inv _ := rfl

def theta3 (n : ℕ) : ℕ := if n=0 then 1 else 2*scan sq n n
def halfTheta (n : ℕ) : ℕ := scan tri n n

theorem theta3Card (n : ℕ) : Nat.card (Fibre intGrade n)=theta3 n := by
  by_cases hn : n=0
  · subst n
    rw [Nat.card_congr intZero]
    simp [theta3]
  · rw [Nat.card_congr (signedSquare n (by omega)), Nat.card_prod,
        boundedCard sq n (fun j h => sqBound j n h)]
    simp [theta3,hn,Nat.mul_comm]

-- Doubled half-integral coordinate: retain the sign as a separate
-- Boolean, with no fictitious zero half-coordinate.
def oddCoord (x : ℕ × Bool) : ℤ :=
  if x.2 then Int.negSucc (2*x.1) else Int.ofNat (2*x.1+1)

def oddDecode (z : ℤ) : ℕ × Bool :=
  match z with
  | .ofNat k => (k/2,false)
  | .negSucc k => (k/2,true)

theorem oddCoordParity (x : ℕ × Bool) : oddCoord x%2=1 := by
  rcases x with ⟨k,b⟩
  cases b <;> simp [oddCoord] <;> omega

theorem oddCoordNorm (x : ℕ × Bool) :
    oddCoord x^2=4*(tri x.1 : ℤ)+1 := by
  rcases x with ⟨k,b⟩
  cases b <;> simp [oddCoord,tri] <;> push_cast <;> ring

theorem oddDecodeEncode (x : ℕ × Bool) : oddDecode (oddCoord x)=x := by
  rcases x with ⟨k,b⟩
  cases b <;> simp [oddCoord,oddDecode] <;> omega

theorem oddEncodeDecode (z : ℤ) (h : z%2=1) : oddCoord (oddDecode z)=z := by
  cases z <;> simp [oddCoord,oddDecode] at * <;> omega

def oddGrade (x : ℕ × Bool) := tri x.1

def oddFibre (n : ℕ) : Fibre oddGrade n ≃ Fibre tri n × Bool where
  toFun x := (⟨x.val.1,x.property⟩,x.val.2)
  invFun x := ⟨(x.1.val,x.2),x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance oddFinite (n : ℕ) : Finite (Fibre oddGrade n) :=
  Finite.of_injective (oddFibre n) (oddFibre n).injective

theorem oddCard (n : ℕ) : Nat.card (Fibre oddGrade n)=2*halfTheta n := by
  rw [Nat.card_congr (oddFibre n),Nat.card_prod,boundedCard tri n (fun j h => triBound j n h)]
  simp [halfTheta,Nat.mul_comm]

-- Norm shell is exactly the grade of the four original coordinates.
def normFibre (n : ℕ) : NormShell n ≃ Fibre (fourGrade intGrade) n where
  toFun x := ⟨((x.val.a,x.val.b),(x.val.c,x.val.d)),by
    have ha := intGradeRead x.val.a
    have hb := intGradeRead x.val.b
    have hc := intGradeRead x.val.c
    have hd := intGradeRead x.val.d
    have he := x.property
    unfold normSq at he
    unfold fourGrade gradePair
    exact_mod_cast (show (intGrade x.val.a : ℤ)+intGrade x.val.b+
      (intGrade x.val.c+intGrade x.val.d)=n by linarith)⟩
  invFun x := ⟨⟨x.val.1.1,x.val.1.2,x.val.2.1,x.val.2.2⟩,by
    have h := x.property
    unfold fourGrade gradePair at h
    have h' : (intGrade x.val.1.1 : ℤ)+intGrade x.val.1.2+
      (intGrade x.val.2.1+intGrade x.val.2.2)=n := by exact_mod_cast h
    unfold normSq
    rw [← intGradeRead x.val.1.1,← intGradeRead x.val.1.2,
      ← intGradeRead x.val.2.1,← intGradeRead x.val.2.2]
    linarith⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem BRead (n : ℕ) : Bcoeff n=(fourth theta3 n : ℤ) := by
  unfold Bcoeff
  rw [Nat.card_congr (normFibre n),fourCard]
  have h : (fun i => Nat.card (Fibre intGrade i)) = theta3 := funext theta3Card
  rw [h]

-- All four half-coordinates are nonzero odd integers, so their
-- doubled norm is 4*(1 + total triangular grade).
theorem halfNoZero : IsEmpty (HalfShell 0) := ⟨fun x => by
  have ha := x.property.2.1
  have h := x.property.1
  unfold normSq at h
  have hz : x.val.a=0 := by nlinarith [sq_nonneg x.val.b,sq_nonneg x.val.c,sq_nonneg x.val.d]
  rw [hz] at ha
  omega⟩

def halfFibre (n : ℕ) : HalfShell (n+1) ≃ Fibre (fourGrade oddGrade) n where
  toFun x := ⟨((oddDecode x.val.a,oddDecode x.val.b),(oddDecode x.val.c,oddDecode x.val.d)),by
    have ha := oddCoordNorm (oddDecode x.val.a)
    have hb := oddCoordNorm (oddDecode x.val.b)
    have hc := oddCoordNorm (oddDecode x.val.c)
    have hd := oddCoordNorm (oddDecode x.val.d)
    rw [oddEncodeDecode _ x.property.2.1] at ha
    rw [oddEncodeDecode _ x.property.2.2.1] at hb
    rw [oddEncodeDecode _ x.property.2.2.2.1] at hc
    rw [oddEncodeDecode _ x.property.2.2.2.2] at hd
    have h := x.property.1
    unfold normSq at h
    unfold fourGrade gradePair oddGrade
    exact_mod_cast (show (tri (oddDecode x.val.a).1 : ℤ)+tri (oddDecode x.val.b).1+
      (tri (oddDecode x.val.c).1+tri (oddDecode x.val.d).1)=n by linarith)⟩
  invFun x := ⟨⟨oddCoord x.val.1.1,oddCoord x.val.1.2,
      oddCoord x.val.2.1,oddCoord x.val.2.2⟩,by
      have h := x.property
      unfold fourGrade gradePair oddGrade at h
      have h' : (tri x.val.1.1.1 : ℤ)+tri x.val.1.2.1+
        (tri x.val.2.1.1+tri x.val.2.2.1)=n := by exact_mod_cast h
      unfold normSq
      simp only [oddCoordNorm]
      push_cast
      linarith,
    oddCoordParity _,oddCoordParity _,oddCoordParity _,oddCoordParity _⟩
  left_inv x := by
    apply Subtype.ext
    apply Quad.ext
    · exact oddEncodeDecode _ x.property.2.1
    · exact oddEncodeDecode _ x.property.2.2.1
    · exact oddEncodeDecode _ x.property.2.2.2.1
    · exact oddEncodeDecode _ x.property.2.2.2.2
  right_inv x := by
    apply Subtype.ext
    simp [oddDecodeEncode]

theorem rowScale (c d : ℕ) (f g : ℕ → ℕ) (n : ℕ) :
    row (fun i => c*f i) (fun i => d*g i) n = c*d*row f g n := by
  unfold row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fourthTwo (f : ℕ → ℕ) (n : ℕ) :
    fourth (fun i => 2*f i) n=16*fourth f n := by
  unfold fourth
  have h : row (fun i => 2*f i) (fun i => 2*f i) =
      fun i => 4*row f f i := by
    funext i
    exact rowScale 2 2 f f i
  rw [h,rowScale]

def Aseries : ℕ → ℕ
  | 0 => 0
  | n+1 => 16*fourth halfTheta n

theorem ARead (n : ℕ) : Acoeff n=(Aseries n : ℤ) := by
  cases n with
  | zero =>
    letI := halfNoZero
    simp [Acoeff,Aseries,Nat.card_eq_zero_of_isEmpty]
  | succ n =>
    unfold Acoeff Aseries
    rw [Nat.card_congr (halfFibre n),fourCard]
    have h : (fun i => Nat.card (Fibre oddGrade i)) = fun i => 2*halfTheta i :=
      funext oddCard
    rw [h,fourthTwo]

def Cseries (n : ℕ) : ℤ :=
  if n%2=0 then (fourth theta3 n : ℤ) else -(fourth theta3 n : ℤ)

theorem CRead (n : ℕ) : Ccoeff n=Cseries n := by
  unfold Ccoeff Cseries
  rw [BRead]

theorem jacobiLiteral (n : ℕ) :
    (fourth theta3 n : ℤ) = (Aseries n : ℤ)+Cseries n := by
  rw [← BRead,← ARead,← CRead]
  exact jacobiShell n

#print axioms pairFibre
#print axioms BRead
#print axioms ARead
#print axioms jacobiLiteral
end
end Integration.Paper9ThetaShellCoefficientWeld
