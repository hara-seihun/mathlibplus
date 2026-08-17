import Mathlib
import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1336OffsetZero

private def chartDifference {G : Type*} [Group G]
    (h : ZMod 7 → G) (i : ZMod 7) : G :=
  (h i)⁻¹ * h (i + 1)

private def chartGeneratedSubgroup {G : Type*} [Group G]
    (h : ZMod 7 → G) : Subgroup G :=
  Subgroup.closure (Set.range (chartDifference h))

private def chartPairSubgroup {G : Type*} [Group G]
    (h : ZMod 7 → G) (r : ZMod 7) : Subgroup (G × G) :=
  Subgroup.closure (Set.range (fun k : ZMod 7 =>
    (chartDifference h k, chartDifference h (k + r))))

private def chartDiagonalRelation {G : Type*} [Group G]
    (L : Subgroup G) : Set (G × G) :=
  {p | ∃ x : L, p = ((x : G), (x : G))}

/-- Claim 30961: at offset zero the generated pair subgroup is the diagonal
of the cyclic-difference subgroup, and every normalized chart value belongs
to that subgroup (equivalently, it is a product of cyclic differences). -/
def offsetZeroPairProjection_claim30961 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
    ∀ h : ZMod 7 → G,
      h 0 = 1 →
      let L := chartGeneratedSubgroup h
      let H₀ := chartPairSubgroup h 0
      (H₀ : Set (G × G)) = chartDiagonalRelation L ∧
        ∀ i : ZMod 7,
          h i ∈ L ∧ (h i, h i) ∈ (H₀ : Set (G × G))

end MathlibPlus.Open.ResearchFormalization.R1336OffsetZero
