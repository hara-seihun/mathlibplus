import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1336

noncomputable section

private def chartDifference30965 {G : Type*} [Group G]
    (h : ZMod 7 → G) (i : ZMod 7) : G :=
  (h i)⁻¹ * h (i + 1)

private def chartGeneratedSubgroup30965 {G : Type*} [Group G]
    (h : ZMod 7 → G) : Subgroup G :=
  Subgroup.closure (Set.range (chartDifference30965 h))

private def chartPairSubgroup30965 {G : Type*} [Group G]
    (h : ZMod 7 → G) (r : ZMod 7) : Subgroup (G × G) :=
  Subgroup.closure (Set.range (fun k : ZMod 7 =>
    (chartDifference30965 h k, chartDifference30965 h (k + r))))

def goursatPairRelation30965
    {G : Type*} [Group G]
    (L : Subgroup G) (N₁ N₂ : Subgroup L)
    [N₁.Normal] [N₂.Normal]
    (φ : (L ⧸ N₁) ≃* (L ⧸ N₂)) : Set (G × G) :=
  {p | ∃ hp : p.1 ∈ L, ∃ hq : p.2 ∈ L,
    φ (QuotientGroup.mk' (N := N₁) (⟨p.1, hp⟩ : L)) =
      QuotientGroup.mk' (N := N₂) (⟨p.2, hq⟩ : L)}

def markedPairRelation30965
    {G : Type*} [Group G]
    (L : Subgroup G) (N₁ N₂ : Subgroup L)
    [N₁.Normal] [N₂.Normal]
    (φ : (L ⧸ N₁) ≃* (L ⧸ N₂))
    (h : ZMod 7 → G) (r i : ZMod 7) : Prop :=
  ∃ hi : chartDifference30965 h i ∈ L,
    ∃ hir : chartDifference30965 h (i + r) ∈ L,
      φ (QuotientGroup.mk' (N := N₁)
          (⟨chartDifference30965 h i, hi⟩ : L)) =
        QuotientGroup.mk' (N := N₂)
          (⟨chartDifference30965 h (i + r), hir⟩ : L)

/-- Goursat's pair-product conclusion, including equal normal kernels and the
marked quotient transport. -/
def claim30965 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
    ∀ h : ZMod 7 → G, h 0 = 1 →
      ∀ r : ZMod 7, r ≠ 0 →
        let L := chartGeneratedSubgroup30965 h
        let H := chartPairSubgroup30965 h r
        ∃ N₁ N₂ : Subgroup L,
          ∃ hN₁ : N₁.Normal, ∃ hN₂ : N₂.Normal,
            letI := hN₁
            letI := hN₂
            ∃ φ : (L ⧸ N₁) ≃* (L ⧸ N₂),
              (H : Set (G × G)) =
                goursatPairRelation30965 L N₁ N₂ φ ∧
              (∀ i : ZMod 7,
                markedPairRelation30965 L N₁ N₂ φ h r i) ∧
              Nat.card N₁ = Nat.card N₂ ∧
              N₁ = N₂

end
end MathlibPlus.Open.ResearchFormalization.R1336
