import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0080

/-- The centered sixth-spline Laplace transform and its zeta expression on the
convergence half-plane.  The two apparent poles in that half-plane are
represented by their removable values. -/
def claim12174 : Prop :=
  let c : ℝ := (32 : ℝ) / 10395
  let g₆ : ℝ → ℝ := fun u =>
    (1 / 12 : ℝ) *
      (∑ n ∈ Finset.Icc 1 (Nat.floor (Real.exp u)),
        (((n : ℝ) / Real.exp u) ^ 2) *
          (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4)
  let β₆ : ℝ → ℝ := fun u => g₆ u - c * Real.exp u
  let D : ℂ → ℂ := fun z =>
    (z + 2) * (z + 4) * (z + 6) * (z + 8) * (z + 10)
  let zetaPoleRemoved : ℂ → ℂ := fun z =>
    if z = (1 : ℂ) then 1 else (z - 1) * riemannZeta z
  let B : ℂ → ℂ := fun z =>
    ∫ u : ℝ in Set.Ioi 0, (β₆ u : ℂ) * Complex.exp (-z * (u : ℂ))
  let H₆ : ℂ → ℂ := fun z => (c : ℂ) + (z - 1) * B z
  let regularizedZetaExpression : ℂ → ℂ := fun z =>
    if z = (1 : ℂ) then
      deriv (fun w : ℂ =>
        (32 : ℂ) * zetaPoleRemoved w / D w - (c : ℂ)) 1
    else if z = (-2 : ℂ) then
      (32 : ℂ) * deriv riemannZeta (-2 : ℂ) /
          (((-2 : ℂ) + 4) * ((-2 : ℂ) + 6) *
            ((-2 : ℂ) + 8) * ((-2 : ℂ) + 10)) -
        (c : ℂ) / ((-2 : ℂ) - 1)
    else
      (32 : ℂ) * riemannZeta z / D z - (c : ℂ) / (z - 1)
  (∀ s : ℂ, -4 < s.re → B s = regularizedZetaExpression s) ∧
    (∀ s : ℂ, H₆ s = (c : ℂ) + (s - 1) * B s)

end MathlibPlus.Open.ResearchFormalization.BatchO0080
