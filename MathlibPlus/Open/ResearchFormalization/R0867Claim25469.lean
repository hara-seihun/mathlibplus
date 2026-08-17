import MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

namespace MathlibPlus.Open.ResearchFormalization.R0867CrossRatioSetup

noncomputable section

abbrev Form (σ : Type*) := MathlibPlus.Open.ResearchFormalization.R0867PackingDegree.Form σ

/-- Claim 25469: four pairwise-distinct nonzero homogeneous forms of one common
`z`-degree, together with the rational denominator-free cross-ratio equation.
The variable carrier is the reviewed multivariable-polynomial carrier, whose
one-variable specialization is `Q(x)[z]`. -/
def homogeneousAllDistinctCrossRatioSetup_claim25469
    {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ) : Prop :=
  (∀ i : Fin 4, K i ≠ 0 ∧
    MvPolynomial.IsHomogeneous (K i) h) ∧
    (∀ ⦃i j : Fin 4⦄, i ≠ j → K i ≠ K j) ∧
    lam ≠ 0 ∧ lam ≠ 1 ∧
    (K 0 - K 3) * (K 1 - K 2) =
      MathlibPlus.Open.ResearchFormalization.R0867PackingDegree.scalarForm lam *
        (K 0 - K 2) * (K 1 - K 3)

end
end MathlibPlus.Open.ResearchFormalization.R0867CrossRatioSetup
