import MathlibPlus.Open.Analysis.AdjacentDefectTransport

namespace MathlibPlus.Open.Analysis

/--
Claim 8667.  The shifted square-root coefficient is tied to the ordinary and
shifted affine-section determinants.  The first equality displays the two
Toeplitz-normalized determinants (with their common `p₀` powers), and the
second equality is the corresponding unnormalized ratio.  The displayed
nonnegativity premise retains the positive-metric branch needed for squaring
`Real.sqrt`.
-/
def exactScalarCancellationInSCoeff_claim8667 : Prop :=
  ∀ (n : ℕ) (p₀ b₀ b : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ),
    N₀.IsSymm → M₀.IsSymm → S_N.IsSymm → S_M.IsSymm →
    N₀.PosDef → M₀.PosDef → p₀ ≠ 0 →
    ∀ (j : ℕ) (h₁j : 1 ≤ j) (hj : j + 1 ≤ n),
      let hj₀ : j ≤ n := Nat.le_trans (Nat.le_succ j) hj
      let hjminus : j - 1 ≤ n :=
        Nat.le_trans (Nat.sub_le j 1) hj₀
      let ratio : ℝ :=
        (sectionDet N₀ S_N b₀ b (j + 1) hj *
          sectionDet M₀ S_M b₀ b (j - 1) hjminus) /
          (sectionDet N₀ S_N b₀ b j hj₀ *
            sectionDet M₀ S_M b₀ b j hj₀)
      0 ≤ ratio →
        sCoeff N₀ M₀ S_N S_M b₀ b j h₁j hj ^ 2 =
            ((sectionDet N₀ S_N b₀ b (j + 1) hj /
                p₀ ^ (2 * (j + 1))) *
              (sectionDet M₀ S_M b₀ b (j - 1) hjminus /
                p₀ ^ (2 * (j - 1)))) /
            ((sectionDet N₀ S_N b₀ b j hj₀ /
                p₀ ^ (2 * j)) *
              (sectionDet M₀ S_M b₀ b j hj₀ /
                p₀ ^ (2 * j))) ∧
          sCoeff N₀ M₀ S_N S_M b₀ b j h₁j hj ^ 2 = ratio

end MathlibPlus.Open.Analysis
