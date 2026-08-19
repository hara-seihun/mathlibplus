import MathlibPlus.Open.Combinatorics.NevilleAllHoleClaim14809

namespace MathlibPlus.Open.Combinatorics.NevilleGamma

noncomputable section

/-- The omitted-hole occupancy condition forces the all-hole interaction to
be maximal on the exact positive Neville-triangle carrier. -/
def localOccupancyControlsTotalInteraction_claim14810 : Prop :=
  ∀ (T : PositiveNevilleTriangle14809) (n : ℕ)
    (H : Finset ℕ),
    1 ≤ n →
      H ⊆ nevilleHoleUniverse14809 n →
        (∀ h : ℕ, h ∈ nevilleHoleUniverse14809 n → h ∉ H →
          nevilleMultiplier14809 T
              (h + 1 + (H.filter (fun h' => h < h')).card) h *
            nevilleSingletonActivity14809 T h ≤ 1) →
          nevilleInteraction14809 T n H ≤
            nevilleInteraction14809 T n (nevilleHoleUniverse14809 n)

end

end MathlibPlus.Open.Combinatorics.NevilleGamma
