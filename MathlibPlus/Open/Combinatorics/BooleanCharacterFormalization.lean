import Mathlib

noncomputable section

open scoped BigOperators

open Classical

namespace MathlibPlus.Open.Combinatorics.BooleanCharacter

/-- The four rank-three chamber labels. -/
abbrev ChamberIndex := Bool × Bool

/-- The bitwise-complement chamber. -/
def chamberComplement (x : ChamberIndex) : ChamberIndex :=
  (Bool.not x.1, Bool.not x.2)

/-- The load in a positive chamber. -/
def chamberLoad (a : ChamberIndex → ℝ)
    (T : ChamberIndex → ChamberIndex → ℝ) (y : ChamberIndex) : ℝ :=
  ∑ x, a x * T x y

/-- Reflection support means that the complement edge is forbidden. -/
def reflectionSupported
    (T : ChamberIndex → ChamberIndex → ℝ) : Prop :=
  ∀ x y, y = chamberComplement x → T x y = 0

/-- Feasibility of a reflection-supported row-stochastic transport matrix. -/
def feasibleReflectionMatrix (a b : ChamberIndex → ℝ)
    (T : ChamberIndex → ChamberIndex → ℝ) : Prop :=
  (∀ x y, 0 ≤ T x y) ∧
    reflectionSupported T ∧
    (∀ x, ∑ y, T x y = 1) ∧
    (∀ y, chamberLoad a T y ≤ b y)

/-- The matrix displayed in the boundary case of Claim 59764. -/
def boundaryReflectionMatrix (a b : ChamberIndex → ℝ)
    (x0 : ChamberIndex) : ChamberIndex → ChamberIndex → ℝ :=
  fun x y =>
    if x = x0 then
      if y = chamberComplement x0 then 0 else b y / a x0
    else if y = chamberComplement x0 then 1 else 0

/-- Claim 59764: rank-three saturation dichotomy. -/
def booleanCharacterRankThreeSaturationDichotomyClaim : Prop :=
  ∀ (a b : ChamberIndex → ℝ),
    (∀ x, 0 < a x) →
    (∀ y, 0 < b y) →
    (∑ x, a x) < ∑ y, b y →
    (∀ x, a x ≤ (∑ y, b y) - b (chamberComplement x)) →
    let A := ∑ x, a x
    let B := ∑ y, b y
    (∀ x x',
      x ≠ x' →
      ¬(a x = B - b (chamberComplement x) ∧
        a x' = B - b (chamberComplement x'))) ∧
      ((∀ x, a x < B - b (chamberComplement x)) ∨
        (∃ x0, a x0 = B - b (chamberComplement x0))) ∧
      ((∀ x, a x < B - b (chamberComplement x)) →
        ∃ T : ChamberIndex → ChamberIndex → ℝ,
          (∀ x y, 0 ≤ T x y) ∧
            reflectionSupported T ∧
            (∀ x, ∑ y, T x y = 1) ∧
            (∀ y, chamberLoad a T y < b y)) ∧
      (∀ x0, a x0 = B - b (chamberComplement x0) →
        (∀ T, feasibleReflectionMatrix a b T →
          (∀ y, y ≠ chamberComplement x0 →
            chamberLoad a T y = b y) ∧
            (∀ x, x ≠ x0 →
              T x (chamberComplement x0) = 1) ∧
            chamberLoad a T (chamberComplement x0) = A - a x0 ∧
            A - a x0 < b (chamberComplement x0)) ∧
        feasibleReflectionMatrix a b (boundaryReflectionMatrix a b x0) ∧
        (∀ x y,
          boundaryReflectionMatrix a b x0 x y =
            if x = x0 then
              if y = chamberComplement x0 then 0 else b y / a x0
            else if y = chamberComplement x0 then 1 else 0))

end MathlibPlus.Open.Combinatorics.BooleanCharacter
