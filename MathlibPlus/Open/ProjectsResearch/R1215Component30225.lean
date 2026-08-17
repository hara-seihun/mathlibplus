import MathlibPlus.Open.ProjectsResearch.R1215

namespace MathlibPlus.Open.ProjectsResearch.R1215Component30225

open MathlibPlus.Open.ProjectsResearch.R1215

/-- The nonzero differences whose translated blocks are disjoint. -/
def zeroIntersectionDifferences (B : Finset C7Squared) : Set C7Squared :=
  {d | d ≠ 0 ∧ translateIntersectionCard B d = 0}

/-- The Cayley graph determined by those zero-intersection differences. -/
def zeroIntersectionCayleyGraph (B : Finset C7Squared) : SimpleGraph C7Squared :=
  SimpleGraph.fromRel (fun g h =>
    g ≠ h ∧ h - g ∈ zeroIntersectionDifferences B)

/-- The graph component containing the identity vertex. -/
def identityComponent (B : Finset C7Squared) : Set C7Squared :=
  {g | SimpleGraph.Reachable (zeroIntersectionCayleyGraph B) 0 g}

/-- Claim 30225: the intrinsic `7K₇` component recovers the additive line and
exactly the six nonzero zero-intersection differences. -/
def claim_30225 : Prop :=
  ∀ (B : Finset C7Squared),
    Nonempty (zeroIntersectionCayleyGraph B ≃g sevenK7) →
      ∃ K : AddSubgroup C7Squared,
        Nat.card K = 7 ∧
          (K : Set C7Squared) = identityComponent B ∧
            ∀ d : C7Squared,
              d ≠ 0 →
                (d ∈ K ↔ translateIntersectionCard B d = 0)

end MathlibPlus.Open.ProjectsResearch.R1215Component30225
