import Mathlib

namespace MathlibPlus.Analysis.Claim44227

noncomputable section

/-- The two unbiased Rademacher values used by the finite two-coordinate model. -/
def sign (o : Bool) : ℝ := if o then 1 else -1

def average (f : Bool → Bool → ℝ) : ℝ :=
  (f false false + f false true + f true false + f true true) / 4

def variance (f : Bool → Bool → ℝ) : ℝ :=
  average (fun o₁ o₂ => (f o₁ o₂ - average f) ^ 2)

def conditionalVarianceFirst (f : Bool → Bool → ℝ) (o₁ : Bool) : ℝ :=
  let m := (f o₁ false + f o₁ true) / 2
  ((f o₁ false - m) ^ 2 + (f o₁ true - m) ^ 2) / 2

def conditionalVarianceSecond (f : Bool → Bool → ℝ) (o₂ : Bool) : ℝ :=
  let m := (f false o₂ + f true o₂) / 2
  ((f false o₂ - m) ^ 2 + (f true o₂ - m) ^ 2) / 2

def firstQueryFirstArea (f : Bool → Bool → ℝ) : ℝ :=
  variance f + (conditionalVarianceFirst f false + conditionalVarianceFirst f true) / 2

def firstQuerySecondArea (f : Bool → Bool → ℝ) : ℝ :=
  variance f + (conditionalVarianceSecond f false + conditionalVarianceSecond f true) / 2

def target (a b d : ℝ) (o₁ o₂ : Bool) : ℝ :=
  a * sign o₁ + b * sign o₂ + d * sign o₁ * sign o₂

def noRepeatOptimum (a b d : ℝ) : ℝ :=
  min (firstQueryFirstArea (target a b d))
    (firstQuerySecondArea (target a b d))

theorem first_query_first_area (a b d : ℝ) :
    firstQueryFirstArea (target a b d) = a ^ 2 + 2 * b ^ 2 + 2 * d ^ 2 := by
  simp [firstQueryFirstArea, variance, average, conditionalVarianceFirst,
    target, sign]
  ring

theorem first_query_second_area (a b d : ℝ) :
    firstQuerySecondArea (target a b d) = 2 * a ^ 2 + b ^ 2 + 2 * d ^ 2 := by
  simp [firstQuerySecondArea, variance, average, conditionalVarianceSecond,
    target, sign]
  ring

theorem no_repeat_optimum (a b d : ℝ) :
    noRepeatOptimum a b d =
      min (a ^ 2 + 2 * b ^ 2 + 2 * d ^ 2)
        (2 * a ^ 2 + b ^ 2 + 2 * d ^ 2) := by
  simp [noRepeatOptimum, first_query_first_area, first_query_second_area]

end

end MathlibPlus.Analysis.Claim44227
