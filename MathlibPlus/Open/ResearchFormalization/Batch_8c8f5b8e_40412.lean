import MathlibPlus.Open.ResearchFormalization.Batch_019ffedc_fb23_7075_84dc_54cb1aa49011

namespace MathlibPlus.Open.ResearchFormalization.ResearchFormalize40412

open MathlibPlus.Open.ResearchFormalizationBatch

private abbrev Plane := MathlibPlus.Open.ResearchFormalizationBatch.Plane

private def gridPoint {p q : ℕ}
    (z u v : Plane) (i : Fin (p + 1)) (j : Fin (q + 1)) : Plane :=
  z + (i.val : ℝ) • u + (j.val : ℝ) • v

private def cornerDisplacementPlus (p q : ℕ) (u v : Plane) : Plane :=
  (p : ℝ) • u + (q : ℝ) • v

private def cornerDisplacementMinus (p q : ℕ) (u v : Plane) : Plane :=
  (p : ℝ) • u - (q : ℝ) • v

private def displacementSq (w : Plane) : ℝ :=
  ∑ i : Fin 2, w i * w i

/-- Claim 40412: opposite corners of a complete unit parallelogram grid
supply both exact squared-displacement identities and the diameter bridge. -/
def claim40412_opposite_corner_diameter_lower_bound : Prop :=
  ∀ (p q : ℕ),
    1 ≤ p →
    1 ≤ q →
    ∀ (u v : Plane),
      (∑ i : Fin 2, u i * u i) = 1 →
      (∑ i : Fin 2, v i * v i) = 1 →
      u 0 * v 1 - u 1 * v 0 ≠ 0 →
      ∀ (X : Finset Plane) (z : Plane),
        (∀ (i : Fin (p + 1)) (j : Fin (q + 1)),
          gridPoint z u v i j ∈ X) →
        let c : ℝ := ∑ i : Fin 2, u i * v i
        let dPlus : Plane := cornerDisplacementPlus p q u v
        let dMinus : Plane := cornerDisplacementMinus p q u v
        (gridPoint z u v ⟨p, Nat.lt_succ_self p⟩
            ⟨q, Nat.lt_succ_self q⟩ -
              gridPoint z u v ⟨0, Nat.zero_lt_succ p⟩
                ⟨0, Nat.zero_lt_succ q⟩ = dPlus) ∧
          (gridPoint z u v ⟨p, Nat.lt_succ_self p⟩
              ⟨0, Nat.zero_lt_succ q⟩ -
              gridPoint z u v ⟨0, Nat.zero_lt_succ p⟩
                ⟨q, Nat.lt_succ_self q⟩ = dMinus) ∧
          displacementSq dPlus =
            (p : ℝ) ^ 2 + (q : ℝ) ^ 2 + 2 * (p : ℝ) * (q : ℝ) * c ∧
          displacementSq dMinus =
            (p : ℝ) ^ 2 + (q : ℝ) ^ 2 - 2 * (p : ℝ) * (q : ℝ) * c ∧
          planarDiameter X ^ 2 ≥ max (displacementSq dPlus)
            (displacementSq dMinus) ∧
          max (displacementSq dPlus) (displacementSq dMinus) =
            (p : ℝ) ^ 2 + (q : ℝ) ^ 2 + 2 * (p : ℝ) * (q : ℝ) * |c| ∧
          (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
              2 * (p : ℝ) * (q : ℝ) * |c| ≥
            (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ∧
          (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ≥ 2 * (p : ℝ) * (q : ℝ)

end MathlibPlus.Open.ResearchFormalization.ResearchFormalize40412
