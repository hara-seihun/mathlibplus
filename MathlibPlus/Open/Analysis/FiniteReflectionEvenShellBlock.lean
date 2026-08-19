import MathlibPlus.Analysis.ThetaMellin

namespace MathlibPlus.Open.Analysis.FiniteReflectionEvenShellBlock

open scoped BigOperators

/-- Claim 11221, with the canonical centered shell
`phi_n(u) = exp(u/2) h(pi*n^2*exp(2*u))` and
`h(x) = (4*x^2 - 6*x)*exp(-x)`. -/
def noNonzeroFiniteReflectionEvenShellBlock_claim11221 : Prop :=
  ∀ (M : ℕ) (n : Fin M → ℕ) (a : Fin M → ℝ),
    (∀ j : Fin M, 0 < n j) →
    Function.Injective n →
    let phi : ℕ → ℝ → ℝ := fun k u =>
      let x : ℝ := Real.pi * (k : ℝ) ^ 2 * Real.exp (2 * u)
      Real.exp (u / 2) * ((4 * x ^ 2 - 6 * x) * Real.exp (-x))
    (∀ u : ℝ,
      (∑ j : Fin M, a j * phi (n j) u) =
        ∑ j : Fin M, a j * phi (n j) (-u)) →
    ∀ j : Fin M, a j = 0

end MathlibPlus.Open.Analysis.FiniteReflectionEvenShellBlock
