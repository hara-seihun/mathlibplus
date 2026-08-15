import MathlibPlus.Open.Formalization.Claim8766

namespace MathlibPlus.Open.Formalization

open scoped BigOperators Topology
open Filter

/-- The coefficient carrier of a positive zero-diagonal finite Jacobi matrix. -/
def positiveZeroDiagonalJacobiCoefficients
    (N : ℕ) (coefficients : ℕ → ℝ) : Prop :=
  coefficients 0 = 0 ∧
    coefficients N = 0 ∧
    ∀ j : ℕ, 1 ≤ j → j < N → 0 < coefficients j

/-- Uniform little-o control of the scaled coefficients on the compact suffix. -/
def uniformlyScaledOnCompactSuffix
    (coefficients : ℕ → ℕ → ℝ) (scale : ℕ → ℝ)
    (profile : ℝ → ℝ) (tau u : ℝ) : Prop :=
  ∃ error : ℕ → ℕ → ℝ,
    (∀ N j : ℕ,
      coefficients N j =
        scale N * (profile ((j : ℝ) / (N : ℝ)) + error N j)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ j : ℕ,
          tau ≤ (j : ℝ) / (N : ℝ) →
          (j : ℝ) / (N : ℝ) ≤ u →
          |error N j| < ε)

/-- Continuum limit of the accumulated forbidden action. -/
def claim8777
    (coefficients : ℕ → ℕ → ℝ) (scale : ℕ → ℝ) (lambda : ℕ → ℝ)
    (profile : ℝ → ℝ) (k m : ℕ → ℕ)
    (tau u ell : ℝ) : Prop :=
  (0 ≤ tau ∧ tau ≤ u ∧ u ≤ 1) ∧
    (∀ N : ℕ,
      positiveZeroDiagonalJacobiCoefficients N (coefficients N)) ∧
    ContinuousOn profile (Set.Icc tau u) ∧
    (∀ t : ℝ, t ∈ Set.Icc tau u → 0 < profile t) ∧
    (∀ t : ℝ, t ∈ Set.Icc tau u → ell ≥ 2 * profile t) ∧
    uniformlyScaledOnCompactSuffix coefficients scale profile tau u ∧
    (∃ error : ℕ → ℝ,
      (∀ N : ℕ, lambda N = scale N * (ell + error N)) ∧
        Tendsto error atTop (𝓝 0)) ∧
    (∀ N : ℕ, 0 < N → k N ≤ m N ∧ m N < N) ∧
    Tendsto (fun N : ℕ => (k N : ℝ) / (N : ℝ)) atTop (𝓝 tau) ∧
    Tendsto (fun N : ℕ => (m N : ℝ) / (N : ℝ)) atTop (𝓝 u) →
      Tendsto
        (fun N : ℕ =>
          (N : ℝ)⁻¹ *
            accumulatedForbiddenAction
              (coefficients N) (lambda N) (k N) (m N))
        atTop
        (𝓝 (∫ t in tau..u, Real.log ((ell - profile t) / profile t)))

end MathlibPlus.Open.Formalization
