import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RankThreeFrameClaim17847

noncomputable section

private def maximalMinor {n : ℕ}
    (M : Matrix (Fin 3) (Fin n) ℝ) (I : Fin 3 → Fin n) : ℝ :=
  Matrix.det (fun i j : Fin 3 => M i (I j))

private def strictAlternating {n : ℕ}
    (M : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  ∀ I : Fin 3 → Fin n, StrictMono I → 0 < maximalMinor M I

private def frameIndex {n : ℕ} (h : 5 ≤ n) (i : Fin 5) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 h⟩

private def columnVector {n : ℕ}
    (M : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : Fin 3 → ℝ :=
  fun i => M i j

private def positiveRankThreeFrame {n : ℕ} (h : 5 ≤ n)
    (M : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  columnVector M (frameIndex h 0) = ![1, 0, 0] ∧
    columnVector M (frameIndex h 1) = ![0, 1, 0] ∧
    columnVector M (frameIndex h 2) = ![0, 0, 1] ∧
    columnVector M (frameIndex h 3) = ![1, -1, 1] ∧
    strictAlternating M

private def projectiveAction {n : ℕ}
    (G : Matrix (Fin 3) (Fin 3) ℝ) (scale : Fin n → ℝ)
    (M : Matrix (Fin 3) (Fin n) ℝ) : Matrix (Fin 3) (Fin n) ℝ :=
  fun i j => (∑ k : Fin 3, G i k * M k j) * scale j

private def projectivelyEquivalent {n : ℕ}
    (M N : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  ∃ (G : Matrix (Fin 3) (Fin 3) ℝ) (scale : Fin n → ℝ),
    0 < Matrix.det G ∧ (∀ j, 0 < scale j) ∧ N = projectiveAction G scale M

private def coordinateA {n : ℕ} (h : 5 ≤ n)
    (M : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : ℝ :=
  maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 0, frameIndex h 1, frameIndex h 3] : Fin 3 → Fin n) k) *
      maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 1, frameIndex h 2, j] : Fin 3 → Fin n) k) /
    (maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 1, frameIndex h 2, frameIndex h 3] : Fin 3 → Fin n) k) *
      maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 0, frameIndex h 1, j] : Fin 3 → Fin n) k))

private def coordinateB {n : ℕ} (h : 5 ≤ n)
    (M : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : ℝ :=
  maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 0, frameIndex h 1, frameIndex h 3] : Fin 3 → Fin n) k) *
      maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 0, frameIndex h 2, j] : Fin 3 → Fin n) k) /
    (maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 0, frameIndex h 2, frameIndex h 3] : Fin 3 → Fin n) k) *
      maximalMinor M (fun k : Fin 3 =>
      (![frameIndex h 0, frameIndex h 1, j] : Fin 3 → Fin n) k))

private def normalizedColumn {n : ℕ}
    (M : Matrix (Fin 3) (Fin n) ℝ) (j : Fin n) : Fin 3 → ℝ :=
  fun i => M i j / M 2 j

private def rankThreeFiveMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 5) ℝ :=
  ![![1, 0, 0, 1, a],
    ![0, 1, 0, -1, -b],
    ![0, 0, 1, 1, 1]]

/-- Claim 17847: the positive rank-three frame has the stated normalized
first four columns; every later labeled column has the exact two minor-ratio
coordinates `(a_j,b_j)`, its normalized column is `(a_j,-b_j,1)`, and those
labeled pairs are a complete quotient chart.  At five points the chamber is
exactly `a₅>b₅>1`. -/
def claim17847_rankThreeFivePointProjectiveChart : Prop :=
  ∀ (n : ℕ) (h : 5 ≤ n)
    (M N : Matrix (Fin 3) (Fin n) ℝ),
    positiveRankThreeFrame h M → positiveRankThreeFrame h N →
      (∀ j : Fin n, 4 ≤ j.1 →
        normalizedColumn M j =
          ![coordinateA h M j, -coordinateB h M j, 1]) ∧
      (∀ j : Fin n, 4 ≤ j.1 →
        normalizedColumn N j =
          ![coordinateA h N j, -coordinateB h N j, 1]) ∧
      ((∀ j : Fin n, 4 ≤ j.1 →
          (coordinateA h M j, coordinateB h M j) =
            (coordinateA h N j, coordinateB h N j)) ↔
        projectivelyEquivalent M N) ∧
      (∀ a b : ℝ,
        strictAlternating (rankThreeFiveMatrix a b) ↔
          a > b ∧ b > 1)

end

end MathlibPlus.Open.ResearchFormalization.RankThreeFrameClaim17847
