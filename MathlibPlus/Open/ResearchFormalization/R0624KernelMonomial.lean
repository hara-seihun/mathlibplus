import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

private def transformedKernelMonomial
    (a b : ℕ) (m : triangularIndex →₀ ℕ) : RootRing :=
  rootZ ^ a * rootX 1 ^ b * eProduct m

private def eFactorCount (m : triangularIndex →₀ ℕ) : ℕ :=
  m.sum (fun _ a => a)

/-- Claim 23457: in the concrete triangular-coordinate carrier of the
scalar rooted-factor algebra, a transformed monomial belonging to the toric
kernel has an `e_r` factor, and the Record-10 generators together with
subalgebra multiplication place every such kernel monomial in `A`; the full
kernel is consequently contained in `A`. -/
def everyToricKernelMonomialLiesInScalarAlgebra_claim23457 : Prop :=
  (∀ (a b : ℕ) (r : triangularIndex),
    transformedKernelMonomial a b (Finsupp.single r 1) ∈
      scalarRootedFactorAlgebra) ∧
  (∀ (a b : ℕ) (m : triangularIndex →₀ ℕ),
    0 < eFactorCount m →
      transformedKernelMonomial a b m ∈ scalarRootedFactorAlgebra) ∧
  (∀ (a b : ℕ) (m : triangularIndex →₀ ℕ),
    transformedKernelMonomial a b m ∈ kernelIdeal →
      0 < eFactorCount m) ∧
  (∀ P : RootRing,
    P ∈ kernelIdeal → P ∈ scalarRootedFactorAlgebra)

end

end MathlibPlus.Open.ResearchFormalization
