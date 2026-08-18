import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.Research.R1724ForestUCoefficient33734

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch

private def componentCount (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun _ a => a)

private def componentWeight (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun k a => k * a)

private def partitionCoefficientSum
    (P : MvPolynomial ℕ ℤ) (d ℓ : ℕ) : ℤ :=
  ∑ m ∈ P.support.filter (fun m =>
    componentWeight m = d ∧ componentCount m = ℓ),
    P.coeff m

/-- Claim 33734: for every tree, the coefficient layer with a positive
    number of parts is the binomial layer, and the all-singleton coefficient
    is one. -/
def claim33734_treeUCoefficientLayer : Prop :=
  ∀ (d : ℕ) (T : SimpleGraph (Fin d)),
    T.IsTree →
      (∀ ℓ : ℕ, 1 ≤ ℓ →
        partitionCoefficientSum (forestUPolynomial T) d ℓ =
          (Nat.choose (d - 1) (ℓ - 1) : ℤ)) ∧
        MvPolynomial.coeff (Finsupp.single 1 d) (forestUPolynomial T) = 1

end

end MathlibPlus.Open.Research.R1724ForestUCoefficient33734
