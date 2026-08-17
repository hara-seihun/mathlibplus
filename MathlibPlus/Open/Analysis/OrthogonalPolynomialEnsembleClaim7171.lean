import MathlibPlus.Open.Analysis.ParticleHole

namespace MathlibPlus.Open.Analysis.OrthogonalPolynomialEnsembleClaim7171

open scoped BigOperators

noncomputable section

/-- Claim 7171: for every admissible cardinality, the orthogonal-polynomial
ensemble partition function is the finite powerset sum of weight products and
the ordered-pair Vandermonde square. -/
def orthogonalPolynomialEnsemblePartitionFunctionClaim7171 : Prop :=
  ∀ (n r : ℕ), r ≤ n →
    ∀ (x w : Fin n → ℝ),
      partitionFunction x w r =
        ∑ s ∈
            (Finset.univ : Finset (Fin n)).powerset.filter
              (fun s => s.card = r),
          (∏ j ∈ s, w j) * vandermondeSq x s

end

end MathlibPlus.Open.Analysis.OrthogonalPolynomialEnsembleClaim7171
