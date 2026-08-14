import Mathlib

namespace MathlibPlus.Analysis.Claim13464

/--
The odd coordinate of the scaled dyadic rotation from claim 13462 vanishes on
its unit input `(cos θ, sin θ)`.  The scale is retained explicitly.
-/
theorem scaledRotation_oddCoordinate_zero_claim13464 (θ : ℝ) :
    (1 / Real.sqrt 2) *
        (-Real.sin θ * Real.cos θ + Real.cos θ * Real.sin θ) = 0 := by
  ring

/--
Consequently this rotated family admits no strictly positive uniform lower
bound for the absolute value of its odd coordinate.
-/
theorem no_positive_uniform_odd_lower_bound_claim13464 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ θ : ℝ,
        c ≤ |(1 / Real.sqrt 2) *
          (-Real.sin θ * Real.cos θ + Real.cos θ * Real.sin θ)| := by
  rintro ⟨c, hc, hbound⟩
  have hz := hbound 0
  norm_num at hz
  linarith

end MathlibPlus.Analysis.Claim13464
