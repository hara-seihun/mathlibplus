import MathlibPlus.Open.Analysis.ParticleHole
import MathlibPlus.Open.Analysis.OrthogonalPolynomialEnsembleClaim7171

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.K0053

noncomputable section

open MathlibPlus.Open.Analysis

/-- The unnormalised one-hole ensemble weight for the node omitted at `j`. -/
def omittedNodeWeight7174 {n : ℕ} (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  (∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, w i) *
    vandermondeSq x ((Finset.univ : Finset (Fin n)).erase j)

/-- Claim 7174: the normalized dual-residue weights are a probability law and
are the normalized weights of the unique omitted node in the `(n - 1)`-particle
ensemble. -/
def claim7174_exactOneHoleProbabilityLaw : Prop :=
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
    let ν : Fin n → ℝ := fun j => h * dualResidueWeight x w j
    (∀ j : Fin n, 0 ≤ ν j) ∧
      (∑ j : Fin n, ν j = 1) ∧
      (∀ j : Fin n,
        ν j = omittedNodeWeight7174 x w j /
          partitionFunction x w (n - 1))

end

end MathlibPlus.Open.NewResearch2.K0053
