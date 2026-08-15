import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The Mellin transform convention on positive real test functions. -/
def mellinTransformConvention
    (f : {x : ℝ // 0 < x} → ℂ) (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ,
    F s =
      ∫ x in Set.Ioi (0 : ℝ),
        if hx : 0 < x then
          f ⟨x, hx⟩ * Complex.cpow (x : ℂ) s / (x : ℂ)
        else
          0

end MathlibPlus.Open.Analysis
