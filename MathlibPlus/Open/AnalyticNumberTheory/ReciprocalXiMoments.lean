import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

noncomputable section

open MeasureTheory Filter
open scoped Topology

/-- Claim 376: the centered completed-xi real carrier is positive, its
reciprocal has superexponential decay, and its Fourier transform is smooth and
even with the displayed reciprocal-moment derivative bounds. -/
def reciprocalXiSmoothnessAndMomentBounds : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let Xc : ℝ → ℂ := fun x => xi ((1 / 2 : ℂ) + (x : ℂ))
  let X : ℝ → ℝ := fun x => (Xc x).re
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) /
      (X x : ℂ)
  let M : ℕ → ℝ := fun n =>
    2 * ∫ x in Set.Ioi (0 : ℝ), x ^ n / X x
  (∀ x, Xc x = (X x : ℂ) ∧ 0 < X x) ∧
    (∀ a : ℝ, 0 < a →
      Tendsto (fun x : ℝ => Real.exp (a * |x|) / X x)
        (cocompact ℝ) (𝓝 0)) ∧
    (∀ n : ℕ, IntegrableOn (fun x : ℝ => x ^ n / X x) (Set.Ioi 0)) ∧
    (∀ t : ℝ, Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) / (X x : ℂ))) ∧
    ContDiff ℝ ⊤ F ∧
    Function.Even F ∧
    ∀ (n : ℕ) (t : ℝ), ‖iteratedDeriv n F t‖ ≤ M n

end

end MathlibPlus.Open.AnalyticNumberTheory
