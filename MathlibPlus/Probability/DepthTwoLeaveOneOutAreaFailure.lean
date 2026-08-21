-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Probability.DepthTwoLeaveOneOutAreaFailure

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

def andTable : Bool → Bool → Bool := fun x y => if x then y else false

def x1Table : Bool → Bool → Bool := fun x _ => x

def x0Table : Bool → Bool → Bool := fun _ y => y

def orTable : Bool → Bool → Bool := fun x y => if x then true else y

def depthAtMostTwo (f : Bool → Bool → Bool) : Prop :=
  (∃ g h : Bool → Bool, ∀ x y, f x y = if x then g y else h y) ∨
  (∃ g h : Bool → Bool, ∀ x y, f x y = if y then g x else h x)

def signedTable (f : Bool → Bool → Bool) : Bool → Bool → ℝ :=
  fun x y => sign (f x y)

def fullTable : Bool → Bool → ℝ := fun x y =>
  (signedTable andTable x y + signedTable x1Table x y +
    signedTable x0Table x y + signedTable orTable x y) / 4

def leaveAnd : Bool → Bool → ℝ := fun x y =>
  (signedTable x1Table x y + signedTable x0Table x y + signedTable orTable x y) / 3

def leaveX1 : Bool → Bool → ℝ := fun x y =>
  (signedTable andTable x y + signedTable x0Table x y + signedTable orTable x y) / 3

def leaveX0 : Bool → Bool → ℝ := fun x y =>
  (signedTable andTable x y + signedTable x1Table x y + signedTable orTable x y) / 3

def leaveOr : Bool → Bool → ℝ := fun x y =>
  (signedTable andTable x y + signedTable x1Table x y + signedTable x0Table x y) / 3

def optimalArea (f : Bool → Bool → ℝ) : ℝ :=
  min (firstQueryFirstArea f) (firstQuerySecondArea f)

end

end MathlibPlus.Probability.DepthTwoLeaveOneOutAreaFailure

namespace MathlibPlus.Open.Probability

open MathlibPlus.Probability.DepthTwoLeaveOneOutAreaFailure

/--
The explicit two-bit depth-two leave-one-out comparison obstruction.  This is
an open registry proposition: its proof is supplied outside `MathlibPlus.Open`.
-/
def depthTwoLeaveOneOutAreaFailure : Prop :=
  depthAtMostTwo andTable ∧
  depthAtMostTwo x1Table ∧
  depthAtMostTwo x0Table ∧
  depthAtMostTwo orTable ∧
  andTable ≠ x1Table ∧
  andTable ≠ x0Table ∧
  andTable ≠ orTable ∧
  x1Table ≠ x0Table ∧
  x1Table ≠ orTable ∧
  x0Table ≠ orTable ∧
  optimalArea fullTable = 3 / 4 ∧
  optimalArea leaveAnd = 29 / 36 ∧
  optimalArea leaveX1 = 2 / 3 ∧
  optimalArea leaveX0 = 2 / 3 ∧
  optimalArea leaveOr = 29 / 36 ∧
  optimalArea fullTable -
      (optimalArea leaveAnd + optimalArea leaveX1 +
        optimalArea leaveX0 + optimalArea leaveOr) / 4 = 1 / 72

end MathlibPlus.Open.Probability

namespace MathlibPlus.Probability.DepthTwoLeaveOneOutAreaFailure

 theorem depthTwoLeaveOneOutAreaFailure_proved :
    MathlibPlus.Open.Probability.depthTwoLeaveOneOutAreaFailure := by
  dsimp [MathlibPlus.Open.Probability.depthTwoLeaveOneOutAreaFailure]
  have h_and : depthAtMostTwo andTable := by
    left
    refine ⟨(fun y => y), (fun _ => false), ?_⟩
    intro x y
    by_cases hx : x
    · simp [andTable, hx]
    · simp [andTable, hx]
  have h_x1 : depthAtMostTwo x1Table := by
    left
    refine ⟨(fun _ => true), (fun _ => false), ?_⟩
    intro x y
    by_cases hx : x <;> simp [x1Table, hx]
  have h_x0 : depthAtMostTwo x0Table := by
    right
    refine ⟨(fun _ => true), (fun _ => false), ?_⟩
    intro x y
    by_cases hy : y <;> simp [x0Table, hy]
  have h_or : depthAtMostTwo orTable := by
    left
    refine ⟨(fun _ => true), (fun y => y), ?_⟩
    intro x y
    by_cases hx : x <;> simp [orTable, hx]
  have hne : andTable ≠ x1Table ∧ andTable ≠ x0Table ∧
      andTable ≠ orTable ∧ x1Table ≠ x0Table ∧
      x1Table ≠ orTable ∧ x0Table ≠ orTable := by
    native_decide
  refine ⟨h_and, h_x1, h_x0, h_or, ?_⟩
  refine ⟨hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1,
    hne.2.2.2.2.1, hne.2.2.2.2.2, ?_⟩
  norm_num [optimalArea, fullTable, leaveAnd, leaveX1, leaveX0, leaveOr,
    signedTable, andTable, x1Table, x0Table, orTable,
    firstQueryFirstArea, firstQuerySecondArea, variance, average,
    conditionalVarianceFirst, conditionalVarianceSecond, sign]

end MathlibPlus.Probability.DepthTwoLeaveOneOutAreaFailure
