import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory.DirichletCoefficientBatch

/-- The coefficient contributed by the differentiated zeta series to the
positive integer `n`. -/
noncomputable def differentiatedZetaCoefficient
    (Q : Polynomial ℝ) (L : ℝ) (n : ℕ) : ℂ :=
  ((Q.eval (Real.log (n : ℝ) / L) : ℝ) : ℂ)

/-- Finite Dirichlet multiplication by `A(s)=∑_{d≤N} a_d d^{-s}` after the
formal differential multiplier.  The finite convolution is written directly
on coefficients, with the divisor condition retained. -/
noncomputable def finiteDifferentiatedProductCoefficient
    (N k : ℕ) (a : ℕ → ℂ) (Q : Polynomial ℝ) (L : ℝ) : ℂ :=
  (Finset.Icc 1 N).sum (fun d =>
    if d ∣ k then a d * differentiatedZetaCoefficient Q L (k / d) else 0)

/-- Finite Dirichlet multiplication by `B(s)=∑_{d≤M} b_d d^{-s}`. -/
noncomputable def finiteZetaProductCoefficient
    (M k : ℕ) (b : ℕ → ℂ) : ℂ :=
  (Finset.Icc 1 M).sum (fun d => if d ∣ k then b d else 0)

/-- The divisor-sum forms appearing in the claim. -/
noncomputable def differentiatedDivisorCoefficient
    (N k : ℕ) (a : ℕ → ℂ) (Q : Polynomial ℝ) (L : ℝ) : ℂ :=
  ((Nat.divisors k).filter (fun d => d ≤ N)).sum (fun d =>
    a d * ((Q.eval (Real.log ((k / d : ℕ) : ℝ) / L) : ℝ) : ℂ))

noncomputable def zetaDivisorCoefficient (M k : ℕ) (b : ℕ → ℂ) : ℂ :=
  ((Nat.divisors k).filter (fun d => d ≤ M)).sum (fun d => b d)

/-- Claim 13809: coefficient extraction gives the two displayed divisor sums,
with the differentiated zeta multiplier retaining the exact `log(k/d)/L`
argument. -/
def claim13809 : Prop :=
  ∀ (N M k : ℕ) (hk : 0 < k)
    (a b : ℕ → ℂ) (Q : Polynomial ℝ) (L : ℝ) (hL : L ≠ 0),
    finiteDifferentiatedProductCoefficient N k a Q L =
        differentiatedDivisorCoefficient N k a Q L ∧
      finiteZetaProductCoefficient M k b = zetaDivisorCoefficient M k b

end MathlibPlus.Open.AnalyticNumberTheory.DirichletCoefficientBatch
