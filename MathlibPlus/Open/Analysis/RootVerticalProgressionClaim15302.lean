import Mathlib

namespace MathlibPlus.Open.Analysis.RootVerticalProgressionClaim15302

/-- Exact open statement of admitted claim 15302: the nonzero roots of a
polynomial in one geometric multiplier lift to complete vertical progressions.
The exponential representation is `q ^ (-s) = exp (-s * log q)`. -/
def claim15302 : Prop :=
  ∀ (q : ℤ) (P : Polynomial ℂ),
    2 ≤ q →
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

end MathlibPlus.Open.Analysis.RootVerticalProgressionClaim15302
