import Mathlib.NumberTheory.Chebyshev

/-!
# Theta partial-summation majorant

This registry node formalizes the exact comparison function and global tail
inequality in admitted claim 638. The function `J` is inlined so that its formula
and the inequality cannot drift apart.
-/

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- With `x₀ = 10^18` and `η = 0.024334`, the packet's theta-based
partial-summation expression majorizes the real prime-counting step function on
the whole half-line `x ≥ x₀`. -/
def thetaPartialSummationMajorant : Prop :=
  let x₀Nat : ℕ := 10 ^ 18
  let x₀ : ℝ := x₀Nat
  let η : ℝ := 12167 / 500000
  ∀ x : ℝ, x₀ ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (Nat.primeCounting x₀Nat : ℝ) -
        Chebyshev.theta x₀ / Real.log x₀ +
        x / Real.log x + η * x / Real.log x ^ 4 +
        ∫ t in x₀..x,
          (1 / Real.log t ^ 2 + η / Real.log t ^ 5)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
