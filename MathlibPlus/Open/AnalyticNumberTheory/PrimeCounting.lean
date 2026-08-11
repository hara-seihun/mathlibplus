import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- For every real `x > 1`, the number of primes at most `x` is strictly below the
explicit eight-term logarithmic majorant whose eighth coefficient is `6097.2`.

Here the real prime-counting function is represented by `Nat.primeCounting ⌊x⌋₊`;
`Nat.primeCounting n` counts the primes at most `n`. Decimal coefficients denote the
exact corresponding rational numbers in `ℝ`.
-/
def globalCoefficient6097Point2 : Prop :=
  ∀ x : ℝ, 1 < x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      let L := Real.log x
      x / L + x / L ^ 2 + 2 * x / L ^ 3 +
        6.024334 * x / L ^ 4 + 24.024334 * x / L ^ 5 +
        120.12167 * x / L ^ 6 + 720.73002 * x / L ^ 7 +
        6097.2 * x / L ^ 8

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
