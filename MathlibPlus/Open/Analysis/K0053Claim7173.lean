import MathlibPlus.Open.Analysis.ParticleHole
import MathlibPlus.Open.Analysis.OrthogonalPolynomialEnsembleClaim7171
import MathlibPlus.Open.NewResearch2.K0053Claim7174

namespace MathlibPlus.Open.Analysis.K0053Claim7173

open scoped BigOperators
open MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 7173: on the exact positive-node finite ensemble interface, the
squared norm of the monic degree-`n-1` orthogonal polynomial, the two adjacent
partition functions, and the dual residue weights satisfy both displayed
normalizations. -/
def claim7173 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ) (P : Polynomial ℝ) (h : ℝ),
    0 < n →
    (StrictMono x ∧ (∀ j : Fin n, 0 < x j) ∧
      (∀ j : Fin n, 0 < w j)) →
    P.Monic →
    P.natDegree = n - 1 →
    (∀ Q : Polynomial ℝ, Q.natDegree < n - 1 →
      (∑ j : Fin n,
        w j * Polynomial.eval (x j) P * Polynomial.eval (x j) Q) = 0) →
    h = ∑ j : Fin n, w j * (Polynomial.eval (x j) P) ^ 2 →
      h = partitionFunction x w n / partitionFunction x w (n - 1) ∧
        (∑ j : Fin n, dualResidueWeight x w j) =
          partitionFunction x w (n - 1) / partitionFunction x w n ∧
        (∑ j : Fin n, dualResidueWeight x w j) = 1 / h

end

end MathlibPlus.Open.Analysis.K0053Claim7173
