import MathlibPlus.Open.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace MathlibPlus.Open.NumberTheory

open scoped ArithmeticFunction.Moebius

/-- Claim 2474: finite multiplicative Möbius inversion on a compactly supported
real half-line function. -/
def moebiusInversion_claim2474 : Prop :=
  ∀ (B : ℝ) (g : ℝ → ℝ),
    (∀ v : ℝ, (v < 1 ∨ B ≤ v) → g v = 0) →
    ∀ u : ℝ, 1 ≤ u →
      let phiPlus : ℝ → ℝ := fun v =>
        ∑' n : ℕ, if 1 ≤ n then (μ n : ℝ) * g ((n : ℝ) * v) else 0
      (∀ v : ℝ, 1 ≤ v →
          Set.Finite {n : ℕ |
            (if 1 ≤ n then (μ n : ℝ) * g ((n : ℝ) * v) else 0) ≠ 0}) ∧
        Set.Finite {m : ℕ |
          (if 1 ≤ m then phiPlus ((m : ℝ) * u) else 0) ≠ 0} ∧
        (∑' m : ℕ, if 1 ≤ m then phiPlus ((m : ℝ) * u) else 0) = g u

end MathlibPlus.Open.NumberTheory
