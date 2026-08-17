import MathlibPlus.Open.FormalizationBatch.K0110
import MathlibPlus.Open.Analysis.AdjacentDefectTransport

namespace MathlibPlus.Open.FormalizationBatch.K0110

open MathlibPlus.Open.Analysis

noncomputable section

/-- Uniform logarithmic transport of each positive determinant-ratio coefficient. -/
def uniformTransportEachRj8668 : Prop :=
  ∀ (n : ℕ) (b b₀ Δ η : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ),
    (hN₀ : N₀.PosDef) →
    (hM₀ : M₀.PosDef) →
    (hNsymm : ∀ t : ℝ, (affinePencil b₀ N₀ S_N t).IsSymm) →
    (hMsymm : ∀ t : ℝ, (affinePencil b₀ M₀ S_M t).IsSymm) →
    let A_N :=
      canonicalInverseSqrt N₀ hN₀ * S_N * canonicalInverseSqrt N₀ hN₀
    let A_M :=
      canonicalInverseSqrt M₀ hM₀ * S_M * canonicalInverseSqrt M₀ hM₀
    let L := max (operatorTwoNorm A_N) (operatorTwoNorm A_M)
    |b - b₀| ≤ Δ →
    η = Δ * L →
    η < 1 →
    ∀ (j : ℕ) (hj : j + 1 ≤ n),
      let rj := rCoeff N₀ M₀ S_N S_M b₀ b j hj
      let rj₀ := rCoeff N₀ M₀ S_N S_M b₀ b₀ j hj
      |Real.log (rj / rj₀)| ≤
        (2 * (j : ℝ) + 1) * (-Real.log (1 - η))

end

end MathlibPlus.Open.FormalizationBatch.K0110
