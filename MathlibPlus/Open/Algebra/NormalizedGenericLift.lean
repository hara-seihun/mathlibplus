import MathlibPlus.Open.Graphs.BasisTranspose

namespace MathlibPlus.Open.Algebra

open scoped BigOperators
open MathlibPlus.Open.Graphs

noncomputable section

/-- The degree-n rational graph-vector space on finite simple-graph
isomorphism classes. -/
abbrev graphSpace5004 (n : ℕ) := GraphIsoClass n →₀ ℚ

/-- A basis vector for a graph-isomorphism class. -/
noncomputable def graphBasis5004 {n : ℕ} (G : GraphIsoClass n) :
    graphSpace5004 n :=
  Finsupp.single G 1

/-- The all-neighborhood vertex-addition basis operator: for every subset of
vertices, adjoin one new vertex with exactly that neighborhood. -/
noncomputable def allNeighborhoodBasis5004 {n : ℕ}
    (H : GraphIsoClass n) : graphSpace5004 (n + 1) :=
  ∑ S : Finset (Fin n),
    graphBasis5004 (graphClass (insertGraph (graphRepresentative H) S))

/-- The unnormalized generic lift on the graph vector space. -/
noncomputable def allNeighborhoodLift5004 (n : ℕ) :
    graphSpace5004 n →ₗ[ℚ] graphSpace5004 (n + 1) :=
  Finsupp.linearCombination ℚ (allNeighborhoodBasis5004 (n := n))

/-- The normalized all-neighborhood basis operator, with the degree factor
`2^(-n)` built into each basis image. -/
noncomputable def normalizedNeighborhoodBasis5004 (n : ℕ)
    (H : GraphIsoClass n) : graphSpace5004 (n + 1) :=
  ((2 : ℚ)⁻¹) ^ n • allNeighborhoodBasis5004 H

/-- The normalized generic lift operator. -/
noncomputable def normalizedGenericLiftOperator5004 (n : ℕ) :
    graphSpace5004 n →ₗ[ℚ] graphSpace5004 (n + 1) :=
  Finsupp.linearCombination ℚ (normalizedNeighborhoodBasis5004 (n := n))

/-- Claim 5004: on the actual rational graph-vector space and the actual
all-neighborhood insertion construction, the normalized degree-n lift is
`2^(-n)` times the unnormalized generic lift. -/
def normalizedGenericLift : Prop :=
  ∀ n : ℕ,
    normalizedGenericLiftOperator5004 n =
      ((2 : ℚ)⁻¹) ^ n • allNeighborhoodLift5004 n

end

end MathlibPlus.Open.Algebra
