import Mathlib
import MathlibPlus.Open.Research.O0020
import MathlibPlus.NumberTheory.Claim9615
import MathlibPlus.NumberTheory.Claim9618

open scoped BigOperators

namespace MathlibPlus.Open.Research

/-- The three tested genesis interfaces have independent counterexamples to their
current proposed invariants. -/
def claim9619 : Prop :=
  (∀ m : ℕ, 0 < m →
    let Q : ℂ → ℂ := fun z => 1 + z ^ (4 * m)
    (∀ x : ℝ,
      Q (x : ℂ) = (1 + x ^ (4 * m) : ℂ) ∧
      Q (Complex.I * (x : ℂ)) = (1 + x ^ (4 * m) : ℂ) ∧
      0 < 1 + x ^ (4 * m)) ∧
    let z : ℂ :=
      Complex.exp (Complex.I * ((Real.pi : ℂ) / (4 * (m : ℂ))))
    Q z = 0 ∧ 0 < z.re ∧ 0 < z.im)
  ∧
  (∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      (n : ι → ℕ) (π : ι → κ → ℝ) (z : ℂ),
      (∀ l, ∑ c, π l c = 1) →
      (∏ l, ∏ c,
        Complex.exp (((π l c : ℂ) * z ^ (n l)) / (n l : ℂ))) =
        ∏ l, Complex.exp (z ^ (n l) / (n l : ℂ)))
  ∧
  Matrix.det MathlibPlus.Open.Research.O0020.reportedScarweaveSusceptibility < 0
  ∧
  (∀ d : ℕ,
    MathlibPlus.NumberTheory.Claim9615.L d =
      MathlibPlus.NumberTheory.Claim9615.R d)
  ∧
  ((35 : ℚ) / 24 ≠ (13 : ℚ) / 8)
  ∧ MathlibPlus.NumberTheory.Claim9618.no_roster_only_euler_recovery

end MathlibPlus.Open.Research
