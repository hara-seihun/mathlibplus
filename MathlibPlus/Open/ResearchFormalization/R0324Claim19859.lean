import MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels

namespace MathlibPlus.Open.ResearchFormalization.R0324Claim19859

open MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels

noncomputable section

/-- Claim 19859: on the exact graph-type `k`-edge subspace, the edge
lowering/raising commutator is the scalar `binom(n,2)-2k`. -/
def claim19859 : Prop :=
  ∀ (n k : ℕ) (x : GraphSpace n),
    edgeHomogeneous n k x →
      ((edgeDeletionOperator n).comp (edgeAdditionOperator n) -
          (edgeAdditionOperator n).comp (edgeDeletionOperator n)) x =
        (((Nat.choose n 2 : ℤ) - 2 * (k : ℤ) : ℤ) : ℚ) • x

end
end MathlibPlus.Open.ResearchFormalization.R0324Claim19859
