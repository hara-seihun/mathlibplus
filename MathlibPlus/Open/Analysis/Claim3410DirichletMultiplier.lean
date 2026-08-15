import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

private noncomputable def dirichletPolynomial
    (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ d ∈ s, c d * Complex.exp (-z * (Real.log (d : ℝ) : ℂ))

private noncomputable def dirichletCenter
    (s : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ s, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

/-- A finite Dirichlet multiplier with the stated pole cancellation and center condition. -/
def finitePoleCancellingDirichletMultiplier
    (s : Finset ℕ) (c : ℕ → ℂ) : Prop :=
  (∀ d ∈ s, 0 < d) ∧
    (∀ d : ℕ, d ∉ s → c d = 0) ∧
    (∑ d ∈ s, c d / (d : ℂ) = 0) ∧
    let A : ℂ → ℂ := dirichletPolynomial s c
    let F : ℂ → ℂ := fun z =>
      if z = 1 then dirichletCenter s c else A z * riemannZeta z
    F 1 ≠ 0

end MathlibPlus.Open.Analysis
