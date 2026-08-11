import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.Analysis.PrimeTheta

/-!
Statement-fidelity formalization of admitted claim 798.  The real Chebyshev
function is Mathlib's `Chebyshev.theta`; the range is the closed ray beginning
at 70111, and the strict bound and objective retain their displayed
quantifiers.  The final conjunct states existence of the supremum as an `IsLUB`
rather than silently choosing an attainment convention.
-/

/-- The fixed-shape theta objective on the range `x ≥ 70111`. -/
def fixedRangeObjective : Prop :=
  let domain : Set ℝ := Set.Ici 70111
  let theta : ℝ → ℝ := Chebyshev.theta
  let F : ℝ → ℝ := fun x =>
    |theta x - x| * Real.log x ^ 4 / x
  (∀ x : ℝ, x ∈ domain → ∀ C : ℝ,
      |theta x - x| < C * x / Real.log x ^ 4 ↔ F x < C) ∧
    (∀ C : ℝ,
      (∀ x : ℝ, x ∈ domain →
        |theta x - x| < C * x / Real.log x ^ 4) ↔
      (∀ x : ℝ, x ∈ domain → F x < C)) ∧
    ∃ s : ℝ, IsLUB (F '' domain) s

end MathlibPlus.Open.Analysis.PrimeTheta
