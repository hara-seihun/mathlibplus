import MathlibPlus.Open.ResearchFormalization.R0634Claim23501

namespace MathlibPlus.Open.ResearchFormalization.R0634Claim23498

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R0634Claim23501

noncomputable section

/-- Claim 23498: the conductor conormal module has the displayed free basis
indexed by `(k,a)` with `k ≥ 2` and `a ≥ 0`, over its scalar quotient
`A/K ≃ ℚ[s]`. -/
def claim_23498 : Prop :=
  Nonempty ((ScalarRing ⧸ scalarRingKernelIdeal) ≃+* Polynomial ℚ) ∧
    ∃ basis : Module.Basis ConormalBasisIndex
        (ScalarRing ⧸ scalarRingKernelIdeal)
        scalarRingKernelIdeal.Cotangent,
      ∀ i : ConormalBasisIndex, ∃ x : scalarRingKernelIdeal,
        ((x : ScalarRing) : RootRing) =
          rootZ ^ i.2 * triangularDifference i.1.1 ∧
          basis i = Ideal.toCotangent scalarRingKernelIdeal x

end

end MathlibPlus.Open.ResearchFormalization.R0634Claim23498
