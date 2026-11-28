import Mathlib
import YangMills.CMP119LiteralResidualSourceDictionary

namespace RequestProject.YangMills

example
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    (dict.toDyadicResidualWeld).regular = dict.literalRegular := by
  rfl

example
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    (dict.toDyadicResidualWeld).rOperation = dict.literalROperation := by
  rfl

example
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    (dict.toDyadicResidualWeld).boundary = dict.literalBoundary := by
  rfl

example
    {L : ℕ}
    (dict : CMP119LiteralResidualSourceDictionary L) :
    (dict.toDyadicResidualWeld).vacuum = dict.literalVacuum := by
  rfl

end RequestProject.YangMills
