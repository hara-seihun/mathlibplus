import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NewResearch2.BatchC0187

noncomputable section

private def finiteDirichletPolynomial (N : ℕ) (c : Fin (N + 1) → ℂ) (s : ℂ) : ℂ :=
  Finset.sum Finset.univ (fun n : Fin (N + 1) =>
    c n * Complex.exp (-s * Complex.log (n.1 + 1 : ℂ)))

private def iteratedComplexDeriv : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f, s => f s
  | n + 1, f, s => deriv (iteratedComplexDeriv n f) s

private def applyDifferentialPolynomial (Q : Polynomial ℂ) (L : ℝ)
    (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  Finset.sum Q.support (fun n =>
    Q.coeff n * ((-1 / (L : ℂ)) ^ n) * iteratedComplexDeriv n f s)

/-- Claim 2773: a finite differential mollifier transfer forces the polynomial
operator to be constant. -/
def finiteDifferentialMollifierTransferObstruction_claim2773 : Prop :=
  ∀ (N M : ℕ) (a : Fin (N + 1) → ℂ) (b : Fin (M + 1) → ℂ)
    (L : ℝ) (Q : Polynomial ℂ),
    0 < L → a 0 ≠ 0 →
      (∀ s : ℂ, 1 < s.re →
        finiteDirichletPolynomial N a s *
            applyDifferentialPolynomial Q L riemannZeta s =
          riemannZeta s * finiteDirichletPolynomial M b s) →
      ∀ n : ℕ, 1 ≤ n → Q.coeff n = 0

end

end MathlibPlus.Open.Analysis.NewResearch2.BatchC0187
