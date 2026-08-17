import MathlibPlus.Open.ResearchFormalizationBatch13782_13785

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch13782_13785

noncomputable section

/-- The positive-support Dirichlet factor `r^(-s)`. -/
noncomputable def positiveDirichletPower (r : ℕ) (s : ℂ) : ℂ :=
  if 0 < r then Complex.cpow (r : ℂ) (-s) else 0

/-- The source-weighted square-Möbius Dirichlet series. -/
noncomputable def sourceWeightedSquareSeries (x : ℝ) (s : ℂ) : ℂ :=
  ∑' r : ℕ,
    (weightedSquareCoefficient x r : ℂ) * positiveDirichletPower r s

/-- Claim 13770: the prime-square value, multiplicative squarefree carrier,
and initially convergent source-weighted Dirichlet series use the exact
Möbius-selected arithmetic data. -/
def claim13770 : Prop :=
  (∀ (x : ℝ) (p : ℕ), Nat.Prime p →
    tauXOnSquare x (p ^ 2) = tauPrimeSquare x p ∧
      (tauPrimeSquare x p : ℂ) =
        1 + Complex.cpow (p : ℂ) (2 * (x : ℂ) * Complex.I) +
          Complex.cpow (p : ℂ) (-2 * (x : ℂ) * Complex.I)) ∧
  (∀ (x : ℝ) (r q : ℕ),
    Nat.Coprime r q → isSquarefree r → isSquarefree q →
      tauXOnSquare x ((r * q) ^ 2) =
        tauXOnSquare x (r ^ 2) * tauXOnSquare x (q ^ 2)) ∧
  (∀ (x : ℝ) (s : ℂ), 1 < s.re →
    Summable (fun r : ℕ =>
      ‖(weightedSquareCoefficient x r : ℂ) * positiveDirichletPower r s‖))

end

end MathlibPlus.Open.ResearchFormalizationBatch13782_13785
