import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Every nonzero root of a nonzero polynomial in a commensurate multiplier has
all of its exponential preimages on one vertical progression, with the stated
critical-line half-plane criterion. -/
def rootVerticalProgressionCorrespondence : Prop :=
  ∀ (q : ℤ) (P : Polynomial ℂ),
    2 ≤ q →
    P ≠ 0 →
    let L : ℝ := Real.log (q : ℝ)
    let r : ℝ := Real.exp (-L / 2)
    ∀ α : ℂ,
      α ≠ 0 →
      P.eval α = 0 →
      let ρ : ℤ → ℂ := fun k =>
        ((-(Real.log ‖α‖) / L : ℝ) : ℂ) -
          Complex.I *
            (((Complex.arg α + 2 * Real.pi * (k : ℝ)) / L : ℝ) : ℂ)
      ({s : ℂ | Complex.exp (-s * (L : ℂ)) = α} =
          {s : ℂ | ∃ k : ℤ, s = ρ k}) ∧
        ((∀ k : ℤ, (ρ k).re > (1 / 2 : ℝ)) ↔ ‖α‖ < r)

end MathlibPlus.Open.Analysis
