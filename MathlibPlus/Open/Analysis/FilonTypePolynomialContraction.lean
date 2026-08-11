import Mathlib

namespace MathlibPlus.Open.Analysis

/-!
Statement-fidelity formalization of admitted claim 5891.

The polynomial and oscillatory kernel are complex-valued, as required by the
factor `exp (i * τ * x)`.  Real nodes are canonically complexified before
polynomial evaluation.  The claim's "distinct nodes on [a,b]" is represented
by injectivity and explicit interval membership.
-/

/-- Exact Filon contraction for a polynomial of degree at most `N`, using the
Lagrange basis at distinct real nodes and the corresponding oscillatory
interval-integral weights. -/
def filonTypePolynomialContraction : Prop :=
  ∀ (N : ℕ) (a b τ : ℝ) (x : Fin (N + 1) → ℝ),
    Function.Injective x →
    (∀ j, x j ∈ Set.Icc a b) →
    ∀ p : Polynomial ℂ, p.natDegree ≤ N →
      let v : Fin (N + 1) → ℂ := fun j => (x j : ℂ)
      let kernel : ℝ → ℂ := fun t =>
        Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ))
      let L : Fin (N + 1) → Polynomial ℂ := fun j =>
        Lagrange.basis Finset.univ v j
      let W : Fin (N + 1) → ℂ := fun j =>
        ∫ t in a..b, (L j).eval (t : ℂ) * kernel t
      (∫ t in a..b, p.eval (t : ℂ) * kernel t) =
        ∑ j, W j * p.eval (x j : ℂ)

end MathlibPlus.Open.Analysis
