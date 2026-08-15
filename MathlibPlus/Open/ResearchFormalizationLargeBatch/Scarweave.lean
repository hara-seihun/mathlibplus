import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch

/-- Load of a fold type (w,s). -/
def scarweaveLoad (p : ℕ × ℕ) : ℕ := 2 * p.1 + p.2

/-- Number of fold types with a positive prescribed load. -/
def scarweaveLoadResolutionCount (ell : ℕ) : ℕ := ell / 2 + 1

/-- A finite one-height presentation, excluding the zero-load fold type. -/
def ScarweavePresentation :=
  {m : (ℕ × ℕ) →₀ ℕ // m (0, 0) = 0}

/-- Total load of a presentation. -/
def scarweavePresentationLoad (X : ScarweavePresentation) : ℕ :=
  ∑ p ∈ X.1.support, X.1 p * scarweaveLoad p

/-- Cycle weight of a presentation. -/
def scarweavePresentationWeight (X : ScarweavePresentation) : ℚ :=
  ∏ p ∈ X.1.support,
    (1 : ℚ) /
      ((X.1 p).factorial *
        ((scarweaveLoad p * scarweaveLoadResolutionCount (scarweaveLoad p) : ℕ) : ℚ) ^
          (X.1 p))

/-- The scarweave cycle-index generating-function identity. -/
def scarweaveCycleIndexGeneratingFunction : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 →
    (∑' X : ScarweavePresentation,
        (scarweavePresentationWeight X : ℂ) *
          z ^ (scarweavePresentationLoad X)) =
      Complex.exp
          (∑' ell : {n : ℕ // 0 < n},
            z ^ (ell.1) / (ell.1 : ℂ)) ∧
      Complex.exp
          (∑' ell : {n : ℕ // 0 < n},
            z ^ (ell.1) / (ell.1 : ℂ)) = 1 / (1 - z)

/-- Unit mass on every load fiber. -/
def scarweaveUnitMassEveryLoadFiber : Prop :=
  ∀ a : ℕ,
    (∑' X : {X : ScarweavePresentation // scarweavePresentationLoad X = a},
      (scarweavePresentationWeight X.1 : ℚ)) = 1

end MathlibPlus.Open.ResearchFormalizationLargeBatch
