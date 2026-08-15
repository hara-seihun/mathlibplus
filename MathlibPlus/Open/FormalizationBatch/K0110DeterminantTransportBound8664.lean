import MathlibPlus.Open.FormalizationBatch.K0110

namespace MathlibPlus.Open.FormalizationBatch.K0110

/-- Determinant transport bound for the leading sections of the two affine pencils. -/
def determinantTransportBound8664 : Prop :=
  ∀ (n : ℕ) (b b₀ Δ η : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ),
    (hN₀ : N₀.PosDef) →
    (hM₀ : M₀.PosDef) →
    (∀ (t : ℝ), (affinePencil b₀ N₀ S_N t).IsSymm) →
    (∀ (t : ℝ), (affinePencil b₀ M₀ S_M t).IsSymm) →
    let N := affinePencil b₀ N₀ S_N
    let M := affinePencil b₀ M₀ S_M
    let A_N :=
      canonicalInverseSqrt N₀ hN₀ * S_N * canonicalInverseSqrt N₀ hN₀
    let A_M :=
      canonicalInverseSqrt M₀ hM₀ * S_M * canonicalInverseSqrt M₀ hM₀
    let L := max (operatorTwoNorm A_N) (operatorTwoNorm A_M)
    |b - b₀| ≤ Δ →
      η = Δ * L →
      η < 1 →
      ∀ (k : ℕ),
        1 ≤ k →
        ∀ (hk : k ≤ n),
          let ℒη := -Real.log (1 - η)
          |Real.log ((leadingSection hk (N b)).det /
              (leadingSection hk (N b₀)).det)| ≤ (k : ℝ) * ℒη ∧
            |Real.log ((leadingSection hk (M b)).det /
              (leadingSection hk (M b₀)).det)| ≤ (k : ℝ) * ℒη

end MathlibPlus.Open.FormalizationBatch.K0110
