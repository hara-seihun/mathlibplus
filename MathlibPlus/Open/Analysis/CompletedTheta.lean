import Mathlib

namespace MathlibPlus.Open.Analysis.CompletedTheta

/-- The four certified Riemann-theta moment balls from admitted claim 348.

The shell, its sum over positive natural indices, and the moments are inlined so
that the numerical statement does not depend on an unaligned auxiliary name.
All displayed decimals elaborate as exact rationals in `ℝ`.
-/
def certifiedFirstFourMoments : Prop :=
  let shell : ℕ → ℝ → ℝ := fun n u ↦
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let phi : ℝ → ℝ := fun u ↦ ∑' n : ℕ, if 1 ≤ n then shell n u else 0
  let moment : ℕ → ℝ := fun j ↦
    2 * ∫ u in Set.Ici (0 : ℝ), phi u * u ^ (2 * j)
  |moment 0 - 0.4971207781883141099127737396854| ≤ (518 : ℝ) / 10 ^ 34 ∧
    |moment 1 - 0.02297194431514543753524987649763217| ≤ (386 : ℝ) / 10 ^ 38 ∧
    |moment 2 - 0.00296284843368763216536829899587642731| ≤ (548 : ℝ) / 10 ^ 41 ∧
    |moment 3 - 0.00059929594659757949184342628260812690661| ≤ (152 : ℝ) / 10 ^ 44

end MathlibPlus.Open.Analysis.CompletedTheta
