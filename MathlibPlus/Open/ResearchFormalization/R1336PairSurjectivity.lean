import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1336.PairSurjectivity

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

private def chartGoursatRelation {G : Type*} [Group G]
    (L : Subgroup G) (N : Subgroup L) (hN : N.Normal) : Set (G × G) :=
  letI := hN
  {p | ∃ hp : p.1 ∈ L, ∃ hq : p.2 ∈ L,
    QuotientGroup.mk' (N := N) (⟨p.1, hp⟩ : L) =
      QuotientGroup.mk' (N := N) (⟨p.2, hq⟩ : L)}

/-- Claim 30968: every normalized common-diagonal Q₁₂ profile is pair-surjective. -/
def universalPairSurjectivity_claim30968 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
    ∀ h : ZMod 7 → G,
      h 0 = 1 →
      let L := chartGeneratedSubgroup h
      let H : ZMod 7 → Subgroup (G × G) :=
        fun r => chartPairSubgroup h r
      (∀ i r : ZMod 7,
        (h i, h (i + r)) ∈ (H r : Set (G × G))) ∧
      (H 0 : Set (G × G)) = chartDiagonalRelation L ∧
      ∀ r : ZMod 7, r ≠ 0 →
        ∃ (N : Subgroup L) (hN : N.Normal),
          (H r : Set (G × G)) = chartGoursatRelation L N hN ∧
          (∀ i : ZMod 7,
            (h i, h (i + r)) ∈ (H r : Set (G × G)))

end MathlibPlus.Open.ResearchFormalization.R1336.PairSurjectivity
