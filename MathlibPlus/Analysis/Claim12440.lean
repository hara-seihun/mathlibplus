import Mathlib

namespace MathlibPlus.Analysis.Claim12440

/-- The exact source radical `{h | h(0) = 0 ∧ ĥ(0) = 0}`.  The Fourier
transform is an explicit source interface so that no normalization convention
is silently chosen. -/
def exactSourceRadical (fourierTransform : (ℝ → ℂ) → ℝ → ℂ) :
    Set (ℝ → ℂ) :=
  {h | h 0 = 0 ∧ fourierTransform h 0 = 0}

end MathlibPlus.Analysis.Claim12440
