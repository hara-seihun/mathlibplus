import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

noncomputable section

/--
Claim 10470.  This is the literal finite-carrier statement: the diagonal
operator has the finite twisted Euler determinant, its logarithmic determinant
has the prime-power expansion, its power traces are the prime-power sums, and
its `s`-derivative has the `log p` weights.

The admitted wording does not specify a convergence region for the logarithmic
series or a branch of the complex logarithm.  The registry node exposes those
choices as the ordinary `Complex.log` and `tsum` expressions below instead of
silently adding hypotheses or replacing the claim by a weaker fragment.
-/
def exactFinitePrimeLocalCarrier_10470 : Prop :=
  ∀ (S : Finset ℕ) (χ : ℕ → ℂ) (s : ℂ),
    (∀ p ∈ S, p.Prime) →
      let ι := {p : ℕ // p ∈ S}
      let w : ℕ → ℂ → ℂ := fun p u =>
        χ p * Complex.exp (-u * (Real.log (p : ℝ) : ℂ))
      let T : ℂ → Matrix ι ι ℂ := fun u =>
        Matrix.diagonal (fun p => w p.1 u)
      (Matrix.det (1 - T s))⁻¹ =
          ∏ p ∈ S, (1 - w p s)⁻¹ ∧
        (∀ m : ℕ, 0 < m →
          Matrix.trace ((T s) ^ m) = ∑ p ∈ S, (w p s) ^ m) ∧
        (-Complex.log (Matrix.det (1 - T s))) =
          (∑' m : ℕ, if 0 < m then
            Matrix.trace ((T s) ^ m) / (m : ℂ) else 0) ∧
        HasDerivAt
          (fun u : ℂ => -Complex.log (Matrix.det (1 - T u)))
          (∑ p ∈ S,
            (-(Real.log (p : ℝ) : ℂ) * w p s) /
              (1 - w p s)) s

end
end MathlibPlus.Open.Analysis
