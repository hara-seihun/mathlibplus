import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0080

/-- The polynomial integration-by-parts identity for the centered sixth
spline port, with the full complex parameter represented by its real and
imaginary coordinates in the convergence half-plane. -/
def polynomialIntegrationByPartsPortFormula_claim12170 : Prop :=
  ∀ (σ t : ℝ), -4 < σ →
    ∀ P : Polynomial ℝ,
      let c : ℝ := (32 : ℝ) / 10395
      let g₆ : ℝ → ℝ := fun u =>
        (1 / 12 : ℝ) *
          (∑ n ∈ Finset.Icc 1 (Nat.floor (Real.exp u)),
            (((n : ℝ) / Real.exp u) ^ 2) *
              (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4)
      let β₆ : ℝ → ℝ := fun u => g₆ u - c * Real.exp u
      let h₆ : ℝ → ℝ := fun u => deriv β₆ u - β₆ u
      let s : ℂ := (σ : ℂ) - Complex.I * (t : ℂ)
      let lhs : ℝ → ℂ := fun u =>
        Polynomial.eval₂ (algebraMap ℝ ℂ) (u : ℂ) P * (h₆ u : ℂ) *
          Complex.exp (-s * (u : ℂ))
      let rhs : ℝ → ℂ := fun u =>
        ((s - 1) * Polynomial.eval₂ (algebraMap ℝ ℂ) (u : ℂ) P -
            Polynomial.eval₂ (algebraMap ℝ ℂ) (u : ℂ) P.derivative) *
          (β₆ u : ℂ) * Complex.exp (-s * (u : ℂ))
      β₆ 0 = -c ∧
        MeasureTheory.IntegrableOn lhs (Set.Ioi 0) ∧
        MeasureTheory.IntegrableOn rhs (Set.Ioi 0) ∧
        (∫ u : ℝ in Set.Ioi 0, lhs u) =
          (c : ℂ) * Polynomial.eval₂ (algebraMap ℝ ℂ) (0 : ℂ) P +
            ∫ u : ℝ in Set.Ioi 0, rhs u

end MathlibPlus.Open.ResearchFormalization.BatchO0080
