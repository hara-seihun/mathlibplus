import Mathlib

namespace MathlibPlus.Open.Analysis.CompletedTheta

/-- The six certified completed-theta moment intervals from admitted claim 369.

The shell, its sum over `n ≥ 1`, and the improper moments are inlined.  Bounds
written in scientific notation in the source are represented by exact rational
quotients in `ℝ`.
-/
def certifiedFirstSixMoments : Prop :=
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
    |moment 3 - 0.00059929594659757949184342628260812690661| ≤ (152 : ℝ) / 10 ^ 44 ∧
    |moment 4 - 0.00016096657455019561088492289700544516005466| ≤ (551 : ℝ) / 10 ^ 47 ∧
    |moment 5 - 0.0000530386342782906547775211837074885956897576| ≤ (304 : ℝ) / 10 ^ 49

end MathlibPlus.Open.Analysis.CompletedTheta
