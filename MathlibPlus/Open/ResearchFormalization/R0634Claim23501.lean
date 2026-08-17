import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Open.ResearchFormalization.R0634Claim23501

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The basis index `(k,a)` for `k≥2` and `a≥0`. -/
abbrev ConormalBasisIndex := triangularIndex × ℕ

/-- Claim 23501: the exact conductor conormal module is a free module over
    the conductor quotient with the displayed `(z^a ē_k)` basis, and is not
    finite as a module over that quotient. -/
def conormalModuleNotFinite_claim23501 : Prop :=
  Nonempty ((ScalarRing ⧸ scalarRingKernelIdeal) ≃+* Polynomial ℚ) ∧
    ¬ Module.Finite (ScalarRing ⧸ scalarRingKernelIdeal)
      scalarRingKernelIdeal.Cotangent ∧
    ∃ basis : Module.Basis ConormalBasisIndex
        (ScalarRing ⧸ scalarRingKernelIdeal)
        scalarRingKernelIdeal.Cotangent,
      ∀ i : ConormalBasisIndex, ∃ x : scalarRingKernelIdeal,
        ((x : ScalarRing) : RootRing) =
          rootZ ^ i.2 * triangularDifference i.1.1 ∧
          basis i = Ideal.toCotangent scalarRingKernelIdeal x

end

end MathlibPlus.Open.ResearchFormalization.R0634Claim23501
