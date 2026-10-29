/-! Secondary mirror of DASHI.Interop.DaysAgoBoundaryExact.
Nat day ordinals are not verified calendar timestamps. -/
namespace AgdaMirror.DaysAgoBoundary

structure DaysAgo where
  referenceDay : Nat
  elapsedDay : Nat
  offsetDays : Nat
  exactOffset : referenceDay = elapsedDay + offsetDays

def makeDaysAgo (elapsed offset : Nat) : DaysAgo :=
  ⟨elapsed + offset, elapsed, offset, rfl⟩

theorem makeDaysAgoReference (elapsed offset : Nat) :
    (makeDaysAgo elapsed offset).referenceDay = elapsed + offset := rfl

theorem makeDaysAgoOffset (elapsed offset : Nat) :
    (makeDaysAgo elapsed offset).offsetDays = offset := rfl

theorem daysAgoEquation (entry : DaysAgo) :
    entry.referenceDay = entry.elapsedDay + entry.offsetDays :=
  entry.exactOffset

end AgdaMirror.DaysAgoBoundary
