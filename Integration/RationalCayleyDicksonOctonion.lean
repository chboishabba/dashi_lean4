import Mathlib

/-!
# Exact rational Cayley-Dickson octonions

Native Lean mirror of the repo's Agda owner
`CayleyDicksonRationalOctonionExact.agda`.

Convention:
  (a,b)(c,d) = (ac - conj(d)b, da + b conj(c)).

This file is deliberately exact/algebraic over `ℚ`; no analytic division-algebra
or exceptional-group claim is made here.
-/

namespace Integration.RationalCayleyDicksonOctonion

structure RationalQuaternion where
  q0 q1 q2 q3 : ℚ
  deriving DecidableEq, Repr

namespace RationalQuaternion

instance : Zero RationalQuaternion := ⟨⟨0,0,0,0⟩⟩
instance : One RationalQuaternion := ⟨⟨1,0,0,0⟩⟩
instance : Add RationalQuaternion := ⟨fun a b =>
  ⟨a.q0+b.q0, a.q1+b.q1, a.q2+b.q2, a.q3+b.q3⟩⟩
instance : Neg RationalQuaternion := ⟨fun a => ⟨-a.q0,-a.q1,-a.q2,-a.q3⟩⟩
instance : Sub RationalQuaternion := ⟨fun a b => a + (-b)⟩

@[ext] theorem ext {a b : RationalQuaternion}
    (h0 : a.q0=b.q0) (h1 : a.q1=b.q1) (h2 : a.q2=b.q2) (h3 : a.q3=b.q3) : a=b := by
  cases a; cases b; simp_all

def conj (a : RationalQuaternion) : RationalQuaternion :=
  ⟨a.q0,-a.q1,-a.q2,-a.q3⟩

def mul (a b : RationalQuaternion) : RationalQuaternion :=
  ⟨ a.q0*b.q0-a.q1*b.q1-a.q2*b.q2-a.q3*b.q3,
    a.q0*b.q1+a.q1*b.q0+a.q2*b.q3-a.q3*b.q2,
    a.q0*b.q2-a.q1*b.q3+a.q2*b.q0+a.q3*b.q1,
    a.q0*b.q3+a.q1*b.q2-a.q2*b.q1+a.q3*b.q0 ⟩

instance : Mul RationalQuaternion := ⟨mul⟩

def normSq (a : RationalQuaternion) : ℚ :=
  a.q0*a.q0+a.q1*a.q1+a.q2*a.q2+a.q3*a.q3

@[simp] theorem conj_involutive (a : RationalQuaternion) : conj (conj a)=a := by
  ext <;> simp [conj]

@[simp] theorem conj_mul (a b : RationalQuaternion) : conj (a*b)=conj b * conj a := by
  ext <;> simp [HMul.hMul, Mul.mul, mul, conj] <;> ring

@[simp] theorem normSq_mul (a b : RationalQuaternion) : normSq (a*b)=normSq a*normSq b := by
  simp [HMul.hMul, Mul.mul, mul, normSq]
  ring

end RationalQuaternion

structure RationalOctonion where
  first second : RationalQuaternion
  deriving DecidableEq, Repr

namespace RationalOctonion

instance : Zero RationalOctonion := ⟨⟨0,0⟩⟩
instance : One RationalOctonion := ⟨⟨1,0⟩⟩
instance : Add RationalOctonion := ⟨fun x y => ⟨x.first+y.first,x.second+y.second⟩⟩
instance : Neg RationalOctonion := ⟨fun x => ⟨-x.first,-x.second⟩⟩
instance : Sub RationalOctonion := ⟨fun x y => x+(-y)⟩
instance : SMul ℚ RationalQuaternion := ⟨fun r q => ⟨r*q.q0,r*q.q1,r*q.q2,r*q.q3⟩⟩
instance : SMul ℚ RationalOctonion := ⟨fun r x => ⟨r • x.first,r • x.second⟩⟩

@[ext] theorem ext {x y : RationalOctonion}
    (h1 : x.first=y.first) (h2 : x.second=y.second) : x=y := by
  cases x; cases y; simp_all

def conj (x : RationalOctonion) : RationalOctonion :=
  ⟨RationalQuaternion.conj x.first, -x.second⟩

def mul (x y : RationalOctonion) : RationalOctonion :=
  ⟨x.first*y.first - RationalQuaternion.conj y.second * x.second,
    y.second*x.first + x.second*RationalQuaternion.conj y.first⟩

instance : Mul RationalOctonion := ⟨mul⟩

def normSq (x : RationalOctonion) : ℚ :=
  RationalQuaternion.normSq x.first + RationalQuaternion.normSq x.second

def realPart (x : RationalOctonion) : ℚ := x.first.q0

@[simp] theorem conj_involutive (x : RationalOctonion) : conj (conj x)=x := by
  ext <;> simp [conj, RationalQuaternion.conj]

@[simp] theorem conj_mul (x y : RationalOctonion) : conj (x*y)=conj y * conj x := by
  ext <;>
    apply RationalQuaternion.ext <;>
    simp [HMul.hMul, Mul.mul, mul, conj, RationalQuaternion.mul,
      RationalQuaternion.conj] <;> ring

@[simp] theorem normSq_mul (x y : RationalOctonion) : normSq (x*y)=normSq x*normSq y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  rcases a with ⟨a0,a1,a2,a3⟩
  rcases b with ⟨b0,b1,b2,b3⟩
  rcases c with ⟨c0,c1,c2,c3⟩
  rcases d with ⟨d0,d1,d2,d3⟩
  simp [normSq, HMul.hMul, Mul.mul, mul, RationalQuaternion.mul,
    RationalQuaternion.normSq, RationalQuaternion.conj]
  ring

/-- Exact left alternativity. -/
theorem left_alternative (x y : RationalOctonion) : (x*x)*y=x*(x*y) := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  rcases c with ⟨c0,c1,c2,c3⟩; rcases d with ⟨d0,d1,d2,d3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [HMul.hMul, Mul.mul, mul, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Exact right alternativity. -/
theorem right_alternative (x y : RationalOctonion) : (x*y)*y=x*(y*y) := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  rcases c with ⟨c0,c1,c2,c3⟩; rcases d with ⟨d0,d1,d2,d3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [HMul.hMul, Mul.mul, mul, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

end RationalOctonion

end Integration.RationalCayleyDicksonOctonion
