import Mathlib

namespace MathlibPlus.Open.PrimeCounting

/-- The published endpoint refutes the strict coefficient-`1.149` bound. -/
def publishedCoefficient1149EndpointCounterexample : Prop :=
  let x₀ : ℕ := 42575222481
  let πx₀ : ℕ := Nat.primeCounting x₀
  let x₀' : ℝ := x₀
  let πx₀' : ℝ := πx₀
  let denominator : ℝ := Real.log x₀' - 1 - (1.149 : ℝ) / Real.log x₀'
  let score : ℝ := Real.log x₀' * (Real.log x₀' - 1 - x₀' / πx₀')
  πx₀ = 1817311115 ∧
    πx₀' - x₀' / denominator > 0 ∧
    score > (1.149 : ℝ) ∧
    ¬ (πx₀' < x₀' / denominator)

end MathlibPlus.Open.PrimeCounting
