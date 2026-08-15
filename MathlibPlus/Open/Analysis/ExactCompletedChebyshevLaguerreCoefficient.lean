import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/--
The completed Chebyshev--Laguerre coefficient at the heat-ray scale, together
with the vanishing of its Laguerre functional on the indicated odd
polynomials.
-/
def exactCompletedChebyshevLaguerreCoefficient : Prop :=
  let generalizedLaguerre : ℕ → ℝ → ℝ → ℝ := fun n α x =>
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k *
        ((∏ j ∈ Finset.Icc (k + 1) n, (α + (j : ℝ))) /
          (Nat.factorial (n - k) : ℝ)) *
        (x ^ k / (Nat.factorial k : ℝ))
  let kernel : ℕ → ℝ → ℝ → ℝ := fun n t u =>
    (Nat.factorial n : ℝ) /
        (2 * Real.sqrt Real.pi * Real.rpow t ((n : ℝ) + (1 / 2 : ℝ))) *
      Real.exp (-(u ^ 2) / (4 * t)) *
        generalizedLaguerre n (-1 / 2 : ℝ) (u ^ 2 / (4 * t))
  let pairing : (ℝ → ℝ) → ℕ → ℝ → ℝ := fun C n t =>
    ∫ u in Set.Ioi (0 : ℝ), C u * deriv (fun v => kernel n t v) u
  ∀ (m : ℕ) (q : ℝ) (Cξ : ℝ → ℝ),
    1 ≤ m → 0 < q →
      pairing Cξ m ((m : ℝ) / q) / kernel m ((m : ℝ) / q) 0 =
          -(1 / generalizedLaguerre m (-1 / 2 : ℝ) 0) *
            (∫ x in Set.Ioi (0 : ℝ),
              Cξ (2 * Real.sqrt ((m : ℝ) * x / q)) *
                Real.exp (-x) * generalizedLaguerre m (1 / 2 : ℝ) x) ∧
        ∀ P : Polynomial ℝ, P.natDegree < m →
          -(1 / generalizedLaguerre m (-1 / 2 : ℝ) 0) *
              (∫ x in Set.Ioi (0 : ℝ),
                ((2 * Real.sqrt ((m : ℝ) * x / q)) *
                  Polynomial.eval
                    ((2 * Real.sqrt ((m : ℝ) * x / q)) ^ 2) P) *
                  Real.exp (-x) * generalizedLaguerre m (1 / 2 : ℝ) x) = 0

end MathlibPlus.Open.Analysis
