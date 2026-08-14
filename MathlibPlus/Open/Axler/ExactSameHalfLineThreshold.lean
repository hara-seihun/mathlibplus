import Mathlib

namespace MathlibPlus.Open.Axler

/--
The exact half-line threshold at the stated endpoint, including its
positive-denominator formulation and the displayed decimal approximation.
-/
def exactSameHalfLineThreshold : Prop :=
  let x₀ : ℝ := 42575222481
  let primeCounting : ℝ → ℝ := fun x =>
    (Nat.primeCounting (Nat.floor x) : ℝ)
  let score : ℝ → ℝ := fun x =>
    Real.log x * (Real.log x - 1 - x / primeCounting x)
  let aStar : ℝ := score x₀
  let denominator : ℝ → ℝ → ℝ := fun c x =>
    Real.log x - 1 - c / Real.log x
  let strictAxlerOnPositiveDomain : ℝ → Prop := fun c =>
    ∀ x : ℝ, x₀ ≤ x → 0 < denominator c x →
      primeCounting x < x / denominator c x
  let displayed : ℝ :=
    (11490003091852194519030898606008869613277 : ℝ) /
      (10 : ℝ) ^ 40
  (∀ x : ℝ, x₀ ≤ x →
      score x ≤ aStar ∧ (score x = aStar → x = x₀)) ∧
    (∀ c : ℝ, c > aStar ↔ strictAxlerOnPositiveDomain c) ∧
    displayed ≤ aStar ∧
      aStar < displayed + 1 / (10 : ℝ) ^ 40

end MathlibPlus.Open.Axler
