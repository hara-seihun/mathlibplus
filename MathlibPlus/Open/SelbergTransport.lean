import MathlibPlus.NumberTheory.Claim15213

open scoped BigOperators

namespace MathlibPlus.Open.SelbergTransport

noncomputable section

/-- Claim 15216: the fixed ordinary-Möbius Selberg recursion reconstructs the
same finite von Mangoldt prefix, so its event-chain difference and canonical
finite path filling have zero relief. -/
def claim15216 : Prop :=
  ∀ (N : ℕ) (a : ArithmeticFunction ℝ),
    2 ≤ N →
    (ha : a 1 = 0) →
    (∀ n, 2 ≤ n → n ≤ N →
      MathlibPlus.NumberTheory.Claim15213.selbergRecursion a ha n =
        MathlibPlus.NumberTheory.Claim15213.lambdaTwo n) →
    (∀ n d, 2 ≤ n → n ≤ N → d ∣ n →
      d ≤ N ∧ n / d ≤ N) ∧
      (∀ n, n ≤ N → a n = ArithmeticFunction.vonMangoldt n) ∧
      (∀ (α : Type*) (v : ℕ → α) (edge : ℕ → α →₀ ℝ)
        (residual : ℕ → ℝ) (eventBoundaryDifference : α →₀ ℝ),
        (∑ j ∈ Finset.range (N + 1), residual j) = 0 →
        eventBoundaryDifference =
          ∑ j ∈ Finset.range (N + 1),
            Finsupp.single (v j) (residual j) →
        (∀ j, j < N →
          edge j =
            Finsupp.single (v (j + 1)) 1 - Finsupp.single (v j) 1) →
        (∀ n, n ≤ N → residual n =
          a n - ArithmeticFunction.vonMangoldt n) →
        (∀ n, n ≤ N → residual n = 0) ∧
          eventBoundaryDifference = 0 ∧
          (∑ j ∈ Finset.range N,
            (-(∑ k ∈ Finset.range (j + 1), residual k)) • edge j) = 0)

end

end MathlibPlus.Open.SelbergTransport
