import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.Jets

/-- The separated bivariate product used for the left/right jet calculation. -/
def separatedProduct (Eₗ Eᵣ : ℝ → ℝ) (l r : ℝ) : ℝ :=
  Eₗ l * Eᵣ r

def partialL (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun l r => deriv (fun x => f x r) l

def partialR (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun l r => deriv (fun y => f l y) r

def dL2R (f : ℝ → ℝ → ℝ) : ℝ :=
  partialL (partialL (partialR f)) 0 0

def dLR2 (f : ℝ → ℝ → ℝ) : ℝ :=
  partialL (partialR (partialR f)) 0 0

def swapOddThird (Eₗ Eᵣ : ℝ → ℝ) : ℝ :=
  dL2R (separatedProduct Eₗ Eᵣ) - dLR2 (separatedProduct Eₗ Eᵣ)

def firstJet (E : ℝ → ℝ) : ℝ := deriv E 0

def secondJetCoefficient (E : ℝ → ℝ) : ℝ := deriv (deriv E) 0 / 2

/-- The degree-two mixed swap-odd jet. -/
def swapOddQuadratic (Eₗ Eᵣ : ℝ → ℝ) : ℝ :=
  partialL (partialR (separatedProduct Eₗ Eᵣ)) 0 0 -
    partialR (partialL (separatedProduct Eₗ Eᵣ)) 0 0

/-- Claim 11740: the first swap-odd coefficient is the displayed degree-three doublet. -/
def claim11740 : Prop :=
  (∀ (Eₗ Eᵣ : ℝ → ℝ),
    ContDiff ℝ 3 Eₗ →
    ContDiff ℝ 3 Eᵣ →
    swapOddThird Eₗ Eᵣ =
      2 * (secondJetCoefficient Eₗ * firstJet Eᵣ -
        firstJet Eₗ * secondJetCoefficient Eᵣ)) ∧
  (∀ (Eₗ Eᵣ : ℝ → ℝ),
    ContDiff ℝ 2 Eₗ →
    ContDiff ℝ 2 Eᵣ →
    swapOddQuadratic Eₗ Eᵣ = 0)

end MathlibPlus.Open.Research.Jets

end
