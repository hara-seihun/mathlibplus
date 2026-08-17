import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RankThreeChamberClaim17848

noncomputable section

private def maximalMinor
    (M : Matrix (Fin 3) (Fin 6) ℝ) (I : Fin 3 → Fin 6) : ℝ :=
  Matrix.det (fun i j : Fin 3 => M i (I j))

private def strictAlternating
    (M : Matrix (Fin 3) (Fin 6) ℝ) : Prop :=
  ∀ I : Fin 3 → Fin 6, StrictMono I → 0 < maximalMinor M I

private def sixPointFrameMatrix (a b c d : ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  ![![1, 0, 0, 1, a, c],
    ![0, 1, 0, -1, -b, -d],
    ![0, 0, 1, 1, 1, 1]]

/-- Claim 17848: for the normalized six-point rank-three frame with fifth
point `(a,-b,1)` and sixth point `(c,-d,1)`, the complete strict alternating
chamber is cut out by exactly the six displayed inequalities. -/
def claim17848_completeSixLabeledAlternatingRankThreeChamber : Prop :=
  ∀ a b c d : ℝ,
    strictAlternating (sixPointFrameMatrix a b c d) ↔
      a > b ∧ b > 1 ∧ c > d ∧ d > 1 ∧ d > b ∧ c > a ∧
        b * c - a * d > 0 ∧
        d - b - a * (d - 1) + c * (b - 1) > 0

end

end MathlibPlus.Open.ResearchFormalization.RankThreeChamberClaim17848
