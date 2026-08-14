import Mathlib

noncomputable section
open Filter

namespace MathlibPlus.Open.ResearchFormalization.C0297

def verifiedHeight : ℕ := 3000175332800

def inverseSquareSlopeCap : ℝ := (verifiedHeight : ℝ) ^ (-2 : ℤ)

def exactVerifiedHeightAndSlopeCap : Prop :=
  verifiedHeight = 3000175332800 ∧
    inverseSquareSlopeCap = (verifiedHeight : ℝ) ^ (-2 : ℤ)

def matchingOrder (d x : ℝ) : ℤ := Int.floor (d * x)

def matchingOrdersEnterRestrictedWindow : Prop :=
  ∀ d : ℝ,
    0 < d ∧ d < inverseSquareSlopeCap →
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        2 ≤ matchingOrder d x ∧
          matchingOrder d x ≤ Int.floor (inverseSquareSlopeCap * x)

def microscopicWindowStillHasUnboundedOrder : Prop :=
  Tendsto (fun x : ℝ => inverseSquareSlopeCap * x) atTop atTop ∧
    ¬ ∃ N : ℕ,
      ∀ᶠ x : ℝ in atTop,
        Int.floor (inverseSquareSlopeCap * x) ≤ (N : ℤ)

end MathlibPlus.Open.ResearchFormalization.C0297
