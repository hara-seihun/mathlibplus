import Mathlib.NumberTheory.Chebyshev
import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.PriorGlobalCoefficient6098

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

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

/-- The coefficient `6097.2` bound is strictly stronger than the predecessor
bound with coefficient `6098`, since `x / (log x)^8` is positive for `x > 1`. -/
theorem globalCoefficient6097Point2_implies_priorGlobalCoefficient6098 :
    MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.globalCoefficient6097Point2 →
      MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.priorGlobalCoefficient6098 := by
  intro h x hx
  let L : ℝ := Real.log x
  let y : ℝ := Nat.primeCounting ⌊x⌋₊
  let R : ℝ :=
    x / L + x / L ^ 2 + 2 * x / L ^ 3 +
      (3012167 / 500000 : ℝ) * x / L ^ 4 +
      (12012167 / 500000 : ℝ) * x / L ^ 5 +
      (12012167 / 100000 : ℝ) * x / L ^ 6 +
      (36036501 / 50000 : ℝ) * x / L ^ 7
  have hlog : 0 < L := by
    dsimp [L]
    exact Real.log_pos hx
  have hterm : 0 < (4 / 5 : ℝ) * x / L ^ 8 := by
    dsimp [L]
    positivity
  have hstrong : y < R + (30486 / 5 : ℝ) * x / L ^ 8 := by
    have hs := h x hx
    dsimp [MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.globalCoefficient6097Point2] at hs
    dsimp [y, R, L]
    norm_num at hs ⊢
    exact hs
  have hgap : R + 6098 * x / L ^ 8 =
      (R + (30486 / 5 : ℝ) * x / L ^ 8) + (4 / 5 : ℝ) * x / L ^ 8 := by
    ring
  have hbound : y < R + 6098 * x / L ^ 8 := by
    rw [hgap]
    linarith
  simpa [MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.priorGlobalCoefficient6098,
    y, R, L] using hbound

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
