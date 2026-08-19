import Mathlib
import MathlibPlus.Analysis.Claim47648

namespace MathlibPlus.Open.ResearchFormalization.R3677

noncomputable section

private def s1LowerBound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (D : ℝ → Y →L[ℂ] X) (δ : ℝ) (x₀ : X) (U : ℝ) : ℝ :=
  Real.exp (δ * U) * ‖x₀‖ / ‖D U‖

private def polynomialLowerBound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (δ : ℝ) (x₀ : X) (K B : ℝ) (U : ℝ) : ℝ :=
  Real.exp (δ * U) * ‖x₀‖ / (K * Real.rpow (1 + U) B)

private def s1PolynomiallyBounded {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (E : ℝ → X →L[ℂ] Y) (δ : ℝ) (x₀ : X) : Prop :=
  ∃ (K' A : ℝ),
    0 < K' ∧ 0 ≤ A ∧
      ∀ U : ℝ, 0 ≤ U →
        ‖E U (Real.exp (δ * U) • x₀)‖ ≤
          K' * Real.rpow (1 + U) A

/-- Claim 47652: polynomial control of the reconstruction family forces the
expanding S1 mode to dominate every fixed polynomial, while polynomial control
of that mode forces the displayed exponential lower bound on reconstruction. -/
def claim47652 : Prop :=
  ∀ {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (E : ℝ → X →L[ℂ] Y) (D : ℝ → Y →L[ℂ] X)
    (δ : ℝ) (x₀ : X),
    0 < δ → x₀ ≠ 0 →
    (∀ (U : ℝ) (x : X), D U (E U x) = x) →
    (∀ (K B : ℝ),
      0 < K → 0 ≤ B →
      (∀ U : ℝ, 0 ≤ U →
        ‖D U‖ ≤ K * Real.rpow (1 + U) B) →
      (∀ U : ℝ, 0 ≤ U →
        s1LowerBound D δ x₀ U ≤
          ‖E U (Real.exp (δ * U) • x₀)‖) ∧
      (∀ U : ℝ, 0 ≤ U →
        polynomialLowerBound δ x₀ K B U ≤
          s1LowerBound D δ x₀ U) ∧
      (∀ N : ℕ,
        Filter.Tendsto
          (fun U : ℝ =>
            polynomialLowerBound δ x₀ K B U /
              (1 + U) ^ N)
          Filter.atTop Filter.atTop) ∧
      ¬ s1PolynomiallyBounded E δ x₀) ∧
    (∀ (K' A : ℝ),
      0 < K' → 0 ≤ A →
      (∀ U : ℝ, 0 ≤ U →
        ‖E U (Real.exp (δ * U) • x₀)‖ ≤
          K' * Real.rpow (1 + U) A) →
      ∀ U : ℝ, 0 ≤ U →
        ‖D U‖ ≥
          Real.exp (δ * U) * ‖x₀‖ /
            (K' * Real.rpow (1 + U) A))

end

end MathlibPlus.Open.ResearchFormalization.R3677
