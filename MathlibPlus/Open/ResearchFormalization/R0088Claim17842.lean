import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0088Claim17842

noncomputable section

private def rankTwoMinor {n : ℕ}
    (A : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  A 0 i * A 1 j - A 1 i * A 0 j

private def rankTwoCrossRatio
    (A : Matrix (Fin 2) (Fin 4) ℝ) : ℝ :=
  rankTwoMinor A 0 2 * rankTwoMinor A 1 3 /
    (rankTwoMinor A 0 1 * rankTwoMinor A 2 3)

private def rankTwoProjectiveAction {n : ℕ}
    (G : Matrix (Fin 2) (Fin 2) ℝ) (scales : Fin n → ℝ)
    (A : Matrix (Fin 2) (Fin n) ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  fun i j => (∑ k : Fin 2, G i k * A k j) * scales j

private def rankTwoProjectivelyEquivalent {n : ℕ}
    (A B : Matrix (Fin 2) (Fin n) ℝ) : Prop :=
  ∃ G : Matrix (Fin 2) (Fin 2) ℝ, ∃ scales : Fin n → ℝ,
    Matrix.det G ≠ 0 ∧ (∀ j, scales j ≠ 0) ∧
      B = rankTwoProjectiveAction G scales A

private def threePointNondegenerate
    (A : Matrix (Fin 2) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ j → rankTwoMinor A i j ≠ 0

private def fourPointNondegenerate
    (A : Matrix (Fin 2) (Fin 4) ℝ) : Prop :=
  ∀ i j : Fin 4, i ≠ j → rankTwoMinor A i j ≠ 0

/-- Claim 17842: on nondegenerate labeled four-point rank-two
configurations, the balanced cross-ratio is a complete invariant for left
`GL₂` and independent nonzero column scaling; three labeled points have no
projective modulus. -/
def rankTwoFourPointCrossRatioComplete_claim17842 : Prop :=
  (∀ A B : Matrix (Fin 2) (Fin 4) ℝ,
    fourPointNondegenerate A → fourPointNondegenerate B →
      (rankTwoCrossRatio A = rankTwoCrossRatio B ↔
        rankTwoProjectivelyEquivalent A B)) ∧
    (∀ A B : Matrix (Fin 2) (Fin 3) ℝ,
      threePointNondegenerate A → threePointNondegenerate B →
        rankTwoProjectivelyEquivalent A B)

end

end MathlibPlus.Open.ResearchFormalization.R0088Claim17842
