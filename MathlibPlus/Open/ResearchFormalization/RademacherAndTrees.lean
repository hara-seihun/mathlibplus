import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

noncomputable section

open scoped BigOperators

/-- The explicit sign convention used for every uniform sign cube below. -/
def researchSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Uniform expectation on a finite type. -/
def uniformAverage {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- The affine Rademacher target attached to a finite coefficient vector. -/
def centeredAffineTargetValue (n : ℕ) (a : Fin n → ℝ)
    (O : Fin n → Bool) : ℝ :=
  ∑ i, a i * researchSign (O i)

/-- The centered-target assertion for the uniform independent sign cube. -/
def centeredAffineTarget : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ),
    uniformAverage (centeredAffineTargetValue n a) = 0

def selectorCMinus : ℝ := -1

def selectorCPlus : ℝ := 1

def selectorIndex0 (r : ℕ) : Fin (r + 3) :=
  ⟨0, by omega⟩

def selectorIndex1 (r : ℕ) : Fin (r + 3) :=
  ⟨1, by omega⟩

def selectorIndex2 (r : ℕ) : Fin (r + 3) :=
  ⟨2, by omega⟩

/-- The specified disagreement atom, with `false` denoting `c₋` and `true` denoting `c₊`. -/
def selectorDisagreement (r : ℕ) (X : Fin (r + 3) → Bool) : Prop :=
  X (selectorIndex0 r) = false ∧
    X (selectorIndex1 r) = true ∧
    X (selectorIndex2 r) = true

def selectorH (r : ℕ) (X : Fin (r + 3) → Bool) : ℝ :=
  researchSign (X (selectorIndex0 r))

def selectorK (r : ℕ) (X : Fin (r + 3) → Bool) : ℝ := by
  classical
  exact if selectorDisagreement r X then selectorCPlus else selectorH r X

noncomputable def selectorDisagreementIndicator
    (r : ℕ) (X : Fin (r + 3) → Bool) : ℝ := by
  classical
  exact if selectorDisagreement r X then 1 else 0

/-- The exact depth-`r+3` atom and its stated probability, moments, covariance, and support. -/
def centeredSharedSelectorAtom : Prop :=
  ∀ r : ℕ,
    uniformAverage (selectorH r) = 0 ∧
      uniformAverage (fun X => selectorH r X * selectorK r X) = (3 : ℝ) / 4 ∧
      uniformAverage (selectorDisagreementIndicator r) = (1 : ℝ) / 8 ∧
      (uniformAverage (fun X => selectorH r X * selectorK r X) -
          uniformAverage (selectorH r) * uniformAverage (selectorK r)) =
        (3 : ℝ) / 4 ∧
      (∀ X, selectorK r X ≠ selectorH r X ↔ selectorDisagreement r X)

/-- The equal-weight shared-selector tree output at coordinate `i`. -/
def sharedSelectorOutput (n : ℕ) (A : Fin n → Bool)
    (yMinus yPlus : Bool) (i : Fin n) : ℝ :=
  if A i then researchSign yPlus else researchSign yMinus

/-- The equal-weight empirical mean of those outputs. -/
def sharedSelectorMu (n : ℕ) (A : Fin n → Bool)
    (yMinus yPlus : Bool) : ℝ :=
  (∑ i, sharedSelectorOutput n A yMinus yPlus i) / (n : ℝ)

/-- A concrete tree syntax for the two displayed fixed-level components. -/
inductive sharedSelectorDepthTwoTree where
  | negY0
  | negY1
  | queryX (whenNegative whenPositive : sharedSelectorDepthTwoTree)

/-- Evaluation of the concrete fixed-level tree syntax. -/
def evaluateSharedSelectorTree : sharedSelectorDepthTwoTree →
    Bool → Bool → Bool → ℝ
  | .negY0, _, y0, _ => -researchSign y0
  | .negY1, _, _, y1 => -researchSign y1
  | .queryX whenNegative whenPositive, x, y0, y1 =>
      if x then
        evaluateSharedSelectorTree whenPositive x y0 y1
      else
        evaluateSharedSelectorTree whenNegative x y0 y1

def sharedSelectorA (x y0 y1 : Bool) : ℝ :=
  -researchSign y1

def sharedSelectorB (x y0 y1 : Bool) : ℝ :=
  if x then -researchSign y0 else -researchSign y1

def sharedSelectorATree : sharedSelectorDepthTwoTree :=
  .queryX .negY1 .negY1

def sharedSelectorBTree : sharedSelectorDepthTwoTree :=
  .queryX .negY1 .negY0

/-- The displayed trees have the stated component values at the common global levels. -/
def sharedSelectorFixedLevelTrees : Prop :=
  ∀ (x y0 y1 : Bool),
    evaluateSharedSelectorTree sharedSelectorATree x y0 y1 =
        sharedSelectorA x y0 y1 ∧
      evaluateSharedSelectorTree sharedSelectorBTree x y0 y1 =
        sharedSelectorB x y0 y1

def sharedSelectorG (x y0 y1 : Bool) : ℝ :=
  (4 : ℝ) / 33 * sharedSelectorA x y0 y1 +
    (29 : ℝ) / 33 * sharedSelectorB x y0 y1

def researchCharacter (S : Finset (Fin 3)) (x : Fin 3 → Bool) : ℝ :=
  S.prod (fun i => researchSign (x i))

def sharedSelectorFourierCoefficient (S : Finset (Fin 3)) : ℝ :=
  uniformAverage (fun x : Fin 3 → Bool =>
    sharedSelectorG (x 0) (x 1) (x 2) * researchCharacter S x)

def sharedSelectorFourierY0 : Finset (Fin 3) := {1}

def sharedSelectorFourierY1 : Finset (Fin 3) := {2}

def sharedSelectorFourierXY0 : Finset (Fin 3) := {0, 1}

def sharedSelectorFourierXY1 : Finset (Fin 3) := {0, 2}

def sharedSelectorFourierSupport : Finset (Finset (Fin 3)) :=
  {sharedSelectorFourierY0, sharedSelectorFourierY1,
    sharedSelectorFourierXY0, sharedSelectorFourierXY1}

def sharedSelectorVariance : ℝ :=
  uniformAverage
    (fun x : Fin 3 → Bool =>
      (sharedSelectorG (x 0) (x 1) (x 2) -
          uniformAverage (fun y : Fin 3 → Bool =>
            sharedSelectorG (y 0) (y 1) (y 2))) ^ 2)

/-- The four Fourier magnitudes, vanishing off the four displayed indices, and variance. -/
def sharedSelectorFourierVariance : Prop :=
  |sharedSelectorFourierCoefficient sharedSelectorFourierY0| = (29 : ℝ) / 66 ∧
    |sharedSelectorFourierCoefficient sharedSelectorFourierY1| = (37 : ℝ) / 66 ∧
    |sharedSelectorFourierCoefficient sharedSelectorFourierXY0| = (29 : ℝ) / 66 ∧
    |sharedSelectorFourierCoefficient sharedSelectorFourierXY1| = (29 : ℝ) / 66 ∧
    (∀ S : Finset (Fin 3), S ∉ sharedSelectorFourierSupport →
      sharedSelectorFourierCoefficient S = 0) ∧
    sharedSelectorVariance = (973 : ℝ) / 1089

end

end ResearchFormalization
end Open
end MathlibPlus
