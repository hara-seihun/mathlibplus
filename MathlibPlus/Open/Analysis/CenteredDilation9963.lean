import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Centered Mellin and derivative `L¹` dilation formulas from admitted Claim 9963. -/
def centeredDilationFormulas9963 : Prop :=
  let mellin : (ℝ → ℂ) → ℂ → ℂ :=
    fun f s => ∫ x in Set.Ioi (0 : ℝ), f x * Complex.cpow (x : ℂ) (s - 1)
  let l1Norm : (ℝ → ℂ) → ℝ :=
    fun f => ∫ x : ℝ, ‖f x‖
  ∀ (c : ℝ) (h : ℝ → ℂ) (s : ℂ),
    let centered : ℝ → ℂ :=
      fun x => (Real.exp (-c / 2) : ℂ) * h (Real.exp (-c) * x)
    let reciprocal : ℝ → ℂ :=
      fun x => (Real.exp (c / 2) : ℂ) * h (Real.exp c * x)
    mellin centered s = Complex.exp ((c : ℂ) * (s - 1 / 2)) * mellin h s ∧
      ∀ (j : ℕ),
        l1Norm (iteratedDeriv j centered) =
            Real.exp (c * (1 / 2 - (j : ℝ))) * l1Norm (iteratedDeriv j h) ∧
          l1Norm (iteratedDeriv j reciprocal) =
            Real.exp (c * ((j : ℝ) - 1 / 2)) * l1Norm (iteratedDeriv j h)

end MathlibPlus.Open.Analysis
