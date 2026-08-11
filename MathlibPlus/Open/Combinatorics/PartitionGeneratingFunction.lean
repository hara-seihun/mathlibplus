import MathlibPlus.Basic

namespace MathlibPlus.Open.Combinatorics

/-- Claim 29356: the number of partitions of `N` into at most `ℓ` parts has
formal generating function `∏_{j=1}^ℓ (1 - X^j)⁻¹`. -/
def partitionAtMostGeneratingFunction : Prop :=
  ∀ ℓ : ℕ,
    let P : ℕ → ℕ := fun N ↦
      (Finset.univ.filter (fun p : Nat.Partition N => p.parts.card ≤ ℓ)).card
    PowerSeries.mk (fun N ↦ (P N : ℚ)) =
      ∏ j ∈ Finset.range ℓ,
        (1 - (PowerSeries.X : PowerSeries ℚ) ^ (j + 1))⁻¹

end MathlibPlus.Open.Combinatorics
