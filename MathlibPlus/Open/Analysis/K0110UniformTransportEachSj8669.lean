import MathlibPlus.Open.Analysis.AdjacentDefectTransport

namespace MathlibPlus.Open.Analysis.K0110

noncomputable section

private abbrev RIndex (n : ℕ) := {j : ℕ // j + 1 ≤ n}

private abbrev SIndex (n : ℕ) := {j : ℕ // 1 ≤ j ∧ j + 1 ≤ n}

private noncomputable def rAt {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) (j : RIndex n) : ℝ :=
  rCoeff N₀ M₀ S_N S_M b₀ b j.1 j.2

private noncomputable def sAt {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) (j : SIndex n) : ℝ :=
  sCoeff N₀ M₀ S_N S_M b₀ b j.1 j.2.1 j.2.2

/-- Uniform transport of each positive `s_j` and of the complete lifted
coefficient family through rank `n`. -/
def uniformTransportEachSj8669 : Prop :=
  ∀ (n : ℕ) (b₀ Δ η : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ),
    N₀.IsSymm → M₀.IsSymm → S_N.IsSymm → S_M.IsSymm →
    N₀.PosDef → M₀.PosDef →
    let A_N := whitenedSlope N₀ S_N
    let A_M := whitenedSlope M₀ S_M
    let L := max (spectralTwoNorm A_N) (spectralTwoNorm A_M)
    let ℒη := -Real.log (1 - η)
    η = Δ * L →
    η < 1 →
    ∀ b : ℝ, |b - b₀| ≤ Δ →
      (∀ j : SIndex n,
        |Real.log (sAt N₀ M₀ S_N S_M b₀ b j /
            sAt N₀ M₀ S_N S_M b₀ b₀ j)| ≤
          2 * (j.1 : ℝ) * ℒη) ∧
      (∀ j : RIndex n,
        |Real.log (rAt N₀ M₀ S_N S_M b₀ b j /
            rAt N₀ M₀ S_N S_M b₀ b₀ j)| ≤
          (2 * (n : ℝ) - 1) * ℒη) ∧
      (∀ j : SIndex n,
        |Real.log (sAt N₀ M₀ S_N S_M b₀ b j /
            sAt N₀ M₀ S_N S_M b₀ b₀ j)| ≤
          (2 * (n : ℝ) - 1) * ℒη)

end

end MathlibPlus.Open.Analysis.K0110
