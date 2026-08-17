import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RankThreeModuliClaim17849

noncomputable section

private def maximalMinor {n : ℕ}
    (M : Matrix (Fin 3) (Fin n) ℝ) (I : Fin 3 → Fin n) : ℝ :=
  Matrix.det (fun i j : Fin 3 => M i (I j))

private def strictAlternating {n : ℕ}
    (M : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  ∀ I : Fin 3 → Fin n, StrictMono I → 0 < maximalMinor M I

private def projectiveAction {n : ℕ}
    (G : Matrix (Fin 3) (Fin 3) ℝ) (scale : Fin n → ℝ)
    (M : Matrix (Fin 3) (Fin n) ℝ) : Matrix (Fin 3) (Fin n) ℝ :=
  fun i j => (∑ k : Fin 3, G i k * M k j) * scale j

private def projectivelyEquivalent {n : ℕ}
    (M N : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  ∃ (G : Matrix (Fin 3) (Fin 3) ℝ) (scale : Fin n → ℝ),
    0 < Matrix.det G ∧ (∀ j, 0 < scale j) ∧ N = projectiveAction G scale M

private def quotientDimension (r n : ℕ) : ℤ :=
  (r : ℤ) * (n : ℤ) - (r : ℤ) ^ 2 - (n : ℤ) + 1

private def rankThreeFiveMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 5) ℝ :=
  ![![1, 0, 0, 1, a],
    ![0, 1, 0, -1, -b],
    ![0, 0, 1, 1, 1]]

private def cellIntegral (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x * Real.rpow ((n : ℝ) + x) (-s - 1)

private def cellSumRange (lo hi : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc lo hi, cellIntegral n s

private def nodeFive (j : Fin 5) : ℝ :=
  (j : ℕ) + 2

private def threeBlockMatrix (u v : ℕ) : Matrix (Fin 3) (Fin 5) ℝ :=
  fun i j =>
    if i.1 = 0 then cellSumRange 1 u (nodeFive j)
    else if i.1 = 1 then cellSumRange (u + 1) v (nodeFive j)
    else cellSumRange (v + 1) 4 (nodeFive j)

private def columnTriple {n : ℕ} (i j k : Fin n) : Fin 3 → Fin n :=
  ![i, j, k]

private def minorThree {n : ℕ} (M : Matrix (Fin 3) (Fin n) ℝ)
    (i j k : Fin n) : ℝ :=
  Matrix.det (fun a b : Fin 3 => M a (columnTriple i j k b))

private def frameCoordinatesFive (M : Matrix (Fin 3) (Fin 5) ℝ) : ℝ × ℝ :=
  (minorThree M 0 1 3 * minorThree M 1 2 4 /
      (minorThree M 1 2 3 * minorThree M 0 1 4),
    minorThree M 0 1 3 * minorThree M 0 2 4 /
      (minorThree M 0 2 3 * minorThree M 0 1 4))

private def threeBlockFramePoint (u v : ℕ) : ℝ × ℝ :=
  frameCoordinatesFive (threeBlockMatrix u v)

/-- Claim 17849: four labeled rank-three points are a projective frame with
no quotient modulus, while the five-point chart is the exact chamber
`a > b > 1`; the explicit five-sample ordered-coarsening data are pairwise
projectively distinct. -/
def claim17849_fiveSamplesSharpForRankThreeProjectiveModuli : Prop :=
  quotientDimension 3 4 = 0 ∧
    quotientDimension 3 5 = 2 ∧
    (∀ M N : Matrix (Fin 3) (Fin 4) ℝ,
      strictAlternating M → strictAlternating N → projectivelyEquivalent M N) ∧
    (∀ a b : ℝ,
      strictAlternating (rankThreeFiveMatrix a b) ↔ a > b ∧ b > 1) ∧
    threeBlockFramePoint 1 2 =
      ((5202290494016311 : ℝ) / 3618030572768076,
        (12417391630898948 : ℝ) / 9534294106705443) ∧
    threeBlockFramePoint 1 3 =
      ((233727306129 : ℝ) / 164203315384,
        (1226117989116 : ℝ) / 945871249981) ∧
    threeBlockFramePoint 2 3 =
      ((307339757596994 : ℝ) / 219735466385799,
        (895782491637604 : ℝ) / 701501238364749) ∧
    threeBlockFramePoint 1 2 ≠ threeBlockFramePoint 1 3 ∧
    threeBlockFramePoint 1 3 ≠ threeBlockFramePoint 2 3 ∧
    threeBlockFramePoint 1 2 ≠ threeBlockFramePoint 2 3

end

end MathlibPlus.Open.ResearchFormalization.RankThreeModuliClaim17849
