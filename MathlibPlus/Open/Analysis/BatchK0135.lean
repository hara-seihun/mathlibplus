import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The ungauged adjacent principal cross-ratio for the lattice heat
Casoratian.  The determinant carrier is the matrix with entries
`q ^ (r*s)` on `Fin k`, as in the admitted lattice statement.
-/
def ungaugedAdjacentPrincipalCrossRatio : Prop :=
  ∀ (γ : ℝ) (n m : ℕ),
    0 < γ →
    1 ≤ n →
    2 ≤ m →
    let q : ℝ := Real.exp (2 * γ / (n : ℝ))
    let D : ℕ → ℝ → ℝ :=
      fun k x => Matrix.det (fun r s : Fin k => x ^ ((r : ℕ) * (s : ℕ)))
    D m q * D (m - 2) q / (D (m - 1) q) ^ 2 =
      q ^ (m - 2) * (q ^ (m - 1) - 1)

end MathlibPlus.Open.Analysis
