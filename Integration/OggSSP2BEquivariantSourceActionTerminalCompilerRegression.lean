import Integration.OggSSP2BEquivariantSourceActionTerminalCompiler

/-! Compile-surface regression: C' must accept weld equivariance directly and
must not require callers to manufacture the conjugation equation by hand. -/

namespace Integration.OggSSP2BEquivariantSourceActionTerminalCompilerRegression

namespace X := Integration.OggSSP2BEquivariantSourceActionTerminalCompiler

example : X.outerActionEqualityIsCompilerOutput = true := rfl

end Integration.OggSSP2BEquivariantSourceActionTerminalCompilerRegression
