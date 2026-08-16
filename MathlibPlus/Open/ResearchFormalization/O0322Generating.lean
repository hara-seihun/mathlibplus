import Mathlib
import MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

namespace MathlibPlus.Open.ResearchFormalization.O0322

noncomputable section

open scoped BigOperators
open MeasureTheory
open Set

open MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

/-- The exact Laplace--Laguerre transform `I_d(δ)` using the reviewed
parameter-two coefficient carrier. -/
noncomputable def laplaceLaguerre15361 (d : ℕ) (δ : ℝ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    Real.exp (-δ * t) * laguerreTwo d t

/-- Claim 15361: the complex generating function of the Laplace--Laguerre
transforms on a sufficiently small complex disk. -/
def claim15361 : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ z : ℂ, ‖z‖ < ρ →
        Summable (fun d : ℕ =>
          (laplaceLaguerre15361 d δ : ℂ) * z ^ d) ∧
          (∑' d : ℕ, (laplaceLaguerre15361 d δ : ℂ) * z ^ d) =
            1 / ((1 - z) ^ 2 *
              ((δ : ℂ) + (1 - (δ : ℂ)) * z))

end

end MathlibPlus.Open.ResearchFormalization.O0322
