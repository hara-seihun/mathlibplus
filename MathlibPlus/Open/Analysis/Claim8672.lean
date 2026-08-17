import MathlibPlus.Open.FormalizationBatch.K0110
import MathlibPlus.Open.Analysis.AdjacentDefectTransport

namespace MathlibPlus.Open.Analysis.Claim8672

open scoped BigOperators

noncomputable section

private abbrev RIndex (n : ℕ) := {j : ℕ // j + 1 ≤ n}

private abbrev SIndex (n : ℕ) := {j : ℕ // 1 ≤ j ∧ j + 1 ≤ n}

private noncomputable def rAt {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) (j : RIndex n) : ℝ :=
  MathlibPlus.Open.Analysis.rCoeff N₀ M₀ S_N S_M b₀ b j.1 j.2

private noncomputable def sAt {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) (j : SIndex n) : ℝ :=
  MathlibPlus.Open.Analysis.sCoeff N₀ M₀ S_N S_M b₀ b
    j.1 j.2.1 j.2.2

private noncomputable def coefficientSet {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) : Set ℝ :=
  {x | (∃ j : RIndex n, x = rAt N₀ M₀ S_N S_M b₀ b j) ∨
    (∃ j : SIndex n, x = sAt N₀ M₀ S_N S_M b₀ b j)}

private noncomputable def minimumCoefficient {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) : ℝ :=
  sInf (coefficientSet N₀ M₀ S_N S_M b₀ b)

/-- Minimum scale transport for the exact interlaced determinant-ratio
coefficient sequence `(r₀,s₁,r₁,…,sₙ₋₁,rₙ₋₁)`. -/
def minimumCoefficientScaleTransport : Prop :=
  ∀ (n : ℕ) (b₀ Δ η : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ),
    0 < n →
    N₀.IsSymm → M₀.IsSymm → S_N.IsSymm → S_M.IsSymm →
    (hN₀ : N₀.PosDef) → (hM₀ : M₀.PosDef) →
    let A_N :=
      MathlibPlus.Open.FormalizationBatch.K0110.canonicalInverseSqrt N₀
        hN₀ * S_N *
        MathlibPlus.Open.FormalizationBatch.K0110.canonicalInverseSqrt N₀
          hN₀
    let A_M :=
      MathlibPlus.Open.FormalizationBatch.K0110.canonicalInverseSqrt M₀
        hM₀ * S_M *
        MathlibPlus.Open.FormalizationBatch.K0110.canonicalInverseSqrt M₀
          hM₀
    let L := max
      (MathlibPlus.Open.FormalizationBatch.K0110.operatorTwoNorm A_N)
      (MathlibPlus.Open.FormalizationBatch.K0110.operatorTwoNorm A_M)
    let ℒη := -Real.log (1 - η)
    η = Δ * L →
    η < 1 →
    ∀ b : ℝ, |b - b₀| ≤ Δ →
      (∀ j : RIndex n,
        0 < rAt N₀ M₀ S_N S_M b₀ b j ∧
        0 < rAt N₀ M₀ S_N S_M b₀ b₀ j ∧
        |Real.log (rAt N₀ M₀ S_N S_M b₀ b j /
            rAt N₀ M₀ S_N S_M b₀ b₀ j)| ≤
          (2 * (j.1 : ℝ) + 1) * ℒη) →
      (∀ j : SIndex n,
        0 < sAt N₀ M₀ S_N S_M b₀ b j ∧
        0 < sAt N₀ M₀ S_N S_M b₀ b₀ j ∧
        |Real.log (sAt N₀ M₀ S_N S_M b₀ b j /
            sAt N₀ M₀ S_N S_M b₀ b₀ j)| ≤
          (2 * (j.1 : ℝ)) * ℒη) →
      0 < minimumCoefficient N₀ M₀ S_N S_M b₀ b ∧
      0 < minimumCoefficient N₀ M₀ S_N S_M b₀ b₀ →
      Real.exp (-(2 * (n : ℝ) - 1) * ℒη) *
          minimumCoefficient N₀ M₀ S_N S_M b₀ b₀ ≤
        minimumCoefficient N₀ M₀ S_N S_M b₀ b ∧
      minimumCoefficient N₀ M₀ S_N S_M b₀ b ≤
        Real.exp ((2 * (n : ℝ) - 1) * ℒη) *
          minimumCoefficient N₀ M₀ S_N S_M b₀ b₀

end

end MathlibPlus.Open.Analysis.Claim8672
