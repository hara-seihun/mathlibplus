import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0314CompletedPair
import MathlibPlus.Open.ResearchFormalization.O0314CompletionCovariance

open scoped BigOperators ComplexConjugate
open Set

namespace MathlibPlus.Open.ResearchFormalization.O0314

noncomputable section

/-- The explicit completed true-line/false-line pair has real-entire,
even, order-one numerators, while the quotient pair is of real type and obeys
the displayed zeta completion covariance. -/
def claim15338 : Prop :=
  ∀ (a b : ℝ),
    0 < a → a < 1 / 2 → 0 < b →
      (∀ k : ℤ, b ≠ (k : ℝ) + 1 / 2) →
      let Eline : ℂ → ℂ := fun z =>
        (z ^ 2 + (b : ℂ) ^ 2) ^ 2
      let Eoff : ℂ → ℂ := fun z =>
        (z ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
          (z ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)
      let Xline : ℂ → ℂ := fun s =>
        Complex.cosh (Real.pi * (s - (1 / 2 : ℂ))) *
          Eline (s - (1 / 2 : ℂ))
      let Xoff : ℂ → ℂ := fun s =>
        Complex.cosh (Real.pi * (s - (1 / 2 : ℂ))) *
          Eoff (s - (1 / 2 : ℂ))
      let C : ℂ → ℂ := standardCompletionFactor
      let χ : ℂ → ℂ := standardCompletionCovarianceFactor
      let Fline : ℂ → ℂ := fun s => Xline s / C s
      let Foff : ℂ → ℂ := fun s => Xoff s / C s
      let realType : (ℂ → ℂ) → Prop := fun f =>
        ∀ s : ℂ, f (star s) = star (f s)
      let realEntire : (ℂ → ℂ) → Prop := fun f =>
        Differentiable ℂ f ∧ realType f
      let evenAboutHalf : (ℂ → ℂ) → Prop := fun f =>
        ∀ s : ℂ, f s = f (1 - s)
      let orderOne : (ℂ → ℂ) → Prop := fun f =>
        (∃ K : ℝ, 0 < K ∧
          ∀ s : ℂ, ‖f s‖ ≤ K * Real.exp (K * ‖s‖)) ∧
        (∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
          ∀ K : ℝ, 0 < K →
            ∃ s : ℂ,
              K * Real.exp (K * Real.rpow ‖s‖ ρ) < ‖f s‖)
      (realEntire Xline ∧ realEntire Xoff) ∧
        (evenAboutHalf Xline ∧ evenAboutHalf Xoff) ∧
        (orderOne Xline ∧ orderOne Xoff) ∧
        (realType Fline ∧ realType Foff) ∧
        (∀ s : ℂ,
          Fline s = χ s * Fline (1 - s) ∧
            Foff s = χ s * Foff (1 - s))

end

end MathlibPlus.Open.ResearchFormalization.O0314
