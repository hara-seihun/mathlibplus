import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6945_sharpInvolution : Prop := by
  exact
    let sharp : (ℂ → ℂ) → (ℂ → ℂ) :=
      fun g z => star (g (-star z))
    (∀ g, sharp (sharp g) = g) ∧
      (∀ (a b : ℂ) (g h : ℂ → ℂ),
        sharp (a • g + b • h) = star a • sharp g + star b • sharp h) ∧
      (∀ (p : ℕ), Nat.Prime p → ∀ g : ℂ → ℂ,
        sharp (fun z => Complex.exp (z * Real.log (p : ℝ)) * g z) =
          (fun z => Complex.exp (-z * Real.log (p : ℝ)) * sharp g z))

end MathlibPlus.Open.ResearchFormalizationLargeBatch
