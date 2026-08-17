import MathlibPlus.NumberTheory.Claim15213

namespace MathlibPlus.Open.SelbergTransport

noncomputable section

/-- A finite-prefix solution of the Selberg recursion for a prescribed right-hand
side.  The uniqueness relation below compares only the coefficients in the
prescribed prefix, rather than arbitrary tails of an arithmetic function. -/
def prefixSolution15215 (N : ℕ) (b : ℕ → ℝ)
    (a : ArithmeticFunction ℝ) : Prop :=
  ∃ ha : a 1 = 0,
    ∀ n : ℕ, 2 ≤ n → n ≤ N →
      MathlibPlus.NumberTheory.Claim15213.selbergRecursion a ha n = b n

/-- Existence together with uniqueness on the finite coefficient prefix. -/
def uniquePrefixSolution15215 (N : ℕ) (b : ℕ → ℝ) : Prop :=
  ∃ a : ArithmeticFunction ℝ,
    prefixSolution15215 N b a ∧
      ∀ a' : ArithmeticFunction ℝ,
        prefixSolution15215 N b a' →
          ∀ n : ℕ, 2 ≤ n → n ≤ N → a' n = a n

/-- Claim 15215: every prescribed finite right-hand side has one causal
Selberg-prefix solution, and the Möbius-log-square right-hand side selects the
von Mangoldt coefficients through Selberg's identity. -/
def claim15215 : Prop :=
  (∀ (N : ℕ) (b : ℕ → ℝ), 2 ≤ N →
    uniquePrefixSolution15215 N b) ∧
  (∀ N : ℕ, 2 ≤ N →
    ∃ hΛ : (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) 1 = 0,
      (∀ n : ℕ, 2 ≤ n → n ≤ N →
        MathlibPlus.NumberTheory.Claim15213.selbergRecursion
            (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) hΛ n =
          MathlibPlus.NumberTheory.Claim15213.lambdaTwo n) ∧
      (∀ a : ArithmeticFunction ℝ,
        prefixSolution15215 N
            (fun n => MathlibPlus.NumberTheory.Claim15213.lambdaTwo n) a →
          ∀ n : ℕ, 2 ≤ n → n ≤ N →
            a n = ArithmeticFunction.vonMangoldt n))

end

end MathlibPlus.Open.SelbergTransport
