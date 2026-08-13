import Mathlib

namespace MathlibPlus.Probability.TwoPairDepthTwoIntrinsicAreaChordFailure

noncomputable section

private def sign (b : Bool) : ℝ := if b then 1 else -1

private def depthAtMostTwo (f : Bool → Bool → Bool) : Prop :=
  (∃ g h : Bool → Bool, ∀ x y, f x y = if x then g y else h y) ∨
  (∃ g h : Bool → Bool, ∀ x y, f x y = if y then g x else h x)

private def average (f : Bool → Bool → ℝ) : ℝ :=
  (f false false + f true false + f false true + f true true) / 4

private def variance (f : Bool → Bool → ℝ) : ℝ :=
  average (fun x y => (f x y - average f) ^ 2)

private def conditionalVarianceFirst (f : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  let m := (f x false + f x true) / 2
  ((f x false - m) ^ 2 + (f x true - m) ^ 2) / 2

private def conditionalVarianceSecond (f : Bool → Bool → ℝ) (y : Bool) : ℝ :=
  let m := (f false y + f true y) / 2
  ((f false y - m) ^ 2 + (f true y - m) ^ 2) / 2

private def firstQueryFirstArea (f : Bool → Bool → ℝ) : ℝ :=
  variance f + (conditionalVarianceFirst f false + conditionalVarianceFirst f true) / 2

private def firstQuerySecondArea (f : Bool → Bool → ℝ) : ℝ :=
  variance f + (conditionalVarianceSecond f false + conditionalVarianceSecond f true) / 2

private def optimalArea (f : Bool → Bool → ℝ) : ℝ :=
  min (firstQueryFirstArea f) (firstQuerySecondArea f)

private def t0 : Bool → Bool → Bool := fun x y =>
  if x then false else if y then false else true

private def t1 : Bool → Bool → Bool := fun _ y => !y

private def t2 : Bool → Bool → Bool := fun x _ => !x

private def t3 : Bool → Bool → Bool := fun x y => if x then true else !y

private def T0 : Bool → Bool → ℝ := fun x y => sign (t0 x y)
private def T1 : Bool → Bool → ℝ := fun x y => sign (t1 x y)
private def T2 : Bool → Bool → ℝ := fun x y => sign (t2 x y)
private def T3 : Bool → Bool → ℝ := fun x y => sign (t3 x y)

private def u : Bool → Bool → ℝ := fun x y => (T0 x y + T1 x y) / 2
private def v : Bool → Bool → ℝ := fun x y => (2 * T2 x y + T3 x y) / 3
private def g : Bool → Bool → ℝ := fun x y =>
  (T0 x y + T1 x y + 2 * T2 x y + T3 x y) / 5

end
end MathlibPlus.Probability.TwoPairDepthTwoIntrinsicAreaChordFailure

namespace MathlibPlus.Open.Probability

open MathlibPlus.Probability.TwoPairDepthTwoIntrinsicAreaChordFailure

/-- A two-bit fixed-pair witness to failure of the outer chord inequality. -/
def twoPairDepthTwoIntrinsicAreaChordFailure : Prop :=
  depthAtMostTwo t0 ∧ depthAtMostTwo t1 ∧ depthAtMostTwo t2 ∧ depthAtMostTwo t3 ∧
  t0 ≠ t1 ∧ t0 ≠ t2 ∧ t0 ≠ t3 ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
  optimalArea u = 13 / 16 ∧
  optimalArea v = 13 / 36 ∧
  optimalArea g = 14 / 25 ∧
  optimalArea g - (2 / 5) * optimalArea u - (3 / 5) * optimalArea v = 11 / 600

end MathlibPlus.Open.Probability

namespace MathlibPlus.Probability.TwoPairDepthTwoIntrinsicAreaChordFailure

 theorem twoPairDepthTwoIntrinsicAreaChordFailure_proved :
    MathlibPlus.Open.Probability.twoPairDepthTwoIntrinsicAreaChordFailure := by
  dsimp [MathlibPlus.Open.Probability.twoPairDepthTwoIntrinsicAreaChordFailure]
  have ht0 : depthAtMostTwo t0 := by
    left
    refine ⟨(fun _ => false), (fun y => if y then false else true), ?_⟩
    intro x y
    by_cases hx : x <;> simp [t0, hx]
  have ht1 : depthAtMostTwo t1 := by
    left
    refine ⟨(fun y => !y), (fun y => !y), ?_⟩
    intro x y
    simp [t1]
  have ht2 : depthAtMostTwo t2 := by
    right
    refine ⟨(fun x => !x), (fun x => !x), ?_⟩
    intro x y
    simp [t2]
  have ht3 : depthAtMostTwo t3 := by
    left
    refine ⟨(fun _ => true), (fun y => !y), ?_⟩
    intro x y
    by_cases hx : x <;> simp [t3, hx]
  have hne : t0 ≠ t1 ∧ t0 ≠ t2 ∧ t0 ≠ t3 ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 := by
    native_decide
  refine ⟨ht0, ht1, ht2, ht3, hne.1, hne.2.1, hne.2.2.1,
    hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2, ?_⟩
  norm_num [optimalArea, u, v, g, T0, T1, T2, T3, t0, t1, t2, t3,
    sign, firstQueryFirstArea, firstQuerySecondArea, variance, average,
    conditionalVarianceFirst, conditionalVarianceSecond]

end MathlibPlus.Probability.TwoPairDepthTwoIntrinsicAreaChordFailure
