import Mathlib

/-!
# General omitted Riemann-theta shell bound

Registry statement for the uniform integral majorant on the first four even
moment orders.
-/

namespace MathlibPlus.Open.Analysis.RiemannTheta

open MeasureTheory Set

/-- For each positive shell label and `k ∈ {0,2,4,6}`, twice the `k`th
half-line moment of the completed Riemann-theta shell is bounded by the
explicit quantity `B_(n,k)`.

The shell formula is inlined so the registry node has no dependency on an
unadmitted definition.
-/
def omittedShellIntegralBound : Prop :=
  ∀ k : ℕ, (k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6) →
    ∀ n : ℕ, 1 ≤ n →
      let Φn : ℝ → ℝ := fun u =>
        (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
          6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
            Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
      let B : ℝ :=
        (8 * Real.pi ^ 2 * (n : ℝ) ^ 4 *
            Real.exp (-Real.pi * (n : ℝ) ^ 2) * (Nat.factorial k : ℝ)) /
          (2 * Real.pi * (n : ℝ) ^ 2 - 9 / 2) ^ (k + 1)
      IntegrableOn (fun u => u ^ k * Φn u) (Ici (0 : ℝ)) ∧
        2 * ∫ u in Ici (0 : ℝ), u ^ k * Φn u ≤ B

end MathlibPlus.Open.Analysis.RiemannTheta
