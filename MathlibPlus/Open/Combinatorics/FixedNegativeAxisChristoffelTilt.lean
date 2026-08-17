import MathlibPlus.Open.Combinatorics.SquaredReciprocalEnsembles

namespace MathlibPlus.Open.Combinatorics

/-- Claim 8920: for each fixed positive `s₀`, the negative-axis
    Christoffel tilt of the squared-Vandermonde ensemble is obtained on the
    same finite-subset carrier by multiplying the base mass by the displayed
    product and dividing by its expectation. -/
def fixedNegativeAxisChristoffelTilt
    (z x ω : ℕ → ℕ+ → ℝ)
    (P : ℕ → Finset ℕ+ → ℝ)
    (Ptilt : ℝ → ℕ → Finset ℕ+ → ℝ) : Prop :=
  ∀ s₀ : ℝ, 0 < s₀ →
    ∀ n : ℕ,
      squaredVandermondeOrthogonalPolynomialEnsemble n z x ω (P n) →
        ∀ S : Finset ℕ+,
          Ptilt s₀ n S =
            (P n S *
                (∏ i ∈ S, (s₀ + (z n i) ^ 2))) /
              (∑' T : Finset ℕ+,
                if T.card = n then
                  P n T * (∏ i ∈ T, (s₀ + (z n i) ^ 2))
                else 0)

end MathlibPlus.Open.Combinatorics
