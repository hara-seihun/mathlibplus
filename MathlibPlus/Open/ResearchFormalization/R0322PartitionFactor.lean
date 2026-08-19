import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0322Claim19813

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0322PartitionFactor

open MathlibPlus.Open.ResearchFormalization.R0322Claim19813

noncomputable section

/-- The shifted-part product in the two-letter coordinates, with
`q=A/W` and `μ_i=λ_i-1`. -/
def shiftedPartProduct_claim19811 {k : ℕ}
    (part : Partition k) : RationalFunction3 :=
  (part.1.map (fun a =>
    1 + x * (A / W) ^ (a - 1))).prod

/-- The exact partition factorization after the `A=Wq` substitution. -/
def claim19811 : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ part : Partition k,
      γ (pPartition part) =
        (1 + W) ^ part.1.length * W ^ (k - part.1.length) *
          shiftedPartProduct_claim19811 part

end
end MathlibPlus.Open.ResearchFormalization.R0322PartitionFactor
