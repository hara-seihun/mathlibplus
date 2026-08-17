import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.NonconfluentCompletionClaim17843

noncomputable section

private def maximalMinor {r n : ℕ}
    (M : Matrix (Fin r) (Fin n) ℝ) (I : Fin r → Fin n) : ℝ :=
  Matrix.det (fun i j : Fin r => M i (I j))

private def columnScale {r n : ℕ}
    (M : Matrix (Fin r) (Fin n) ℝ) (scale : Fin n → ℝ) :
    Matrix (Fin r) (Fin n) ℝ :=
  fun i j => M i j * scale j

private def strictAlternating {r n : ℕ}
    (M : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∀ I : Fin r → Fin n, StrictMono I → 0 < maximalMinor M I

private def sameChirotope {r n : ℕ}
    (M N : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∀ I : Fin r → Fin n, Function.Injective I →
    ((0 < maximalMinor M I ↔ 0 < maximalMinor N I) ∧
      (maximalMinor M I = 0 ↔ maximalMinor N I = 0) ∧
      (maximalMinor M I < 0 ↔ maximalMinor N I < 0))

private def fixedChirotopeProjectiveAction {r n : ℕ}
    (G : Matrix (Fin r) (Fin r) ℝ) (scale : Fin n → ℝ)
    (M : Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin r) (Fin n) ℝ :=
  fun i j => (∑ k : Fin r, G i k * M k j) * scale j

private def fixedChirotopeProjectivelyEquivalent {r n : ℕ}
    (M N : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∃ (G : Matrix (Fin r) (Fin r) ℝ) (scale : Fin n → ℝ),
    0 < Matrix.det G ∧ (∀ j, 0 < scale j) ∧
      N = fixedChirotopeProjectiveAction G scale M

private def balancedColumnOccurrence {r n : ℕ}
    (I J K L : Fin r → Fin n) : Prop :=
  ∀ x : Fin n,
    (∑ i : Fin r, if I i = x then (1 : ℕ) else 0) +
        (∑ i : Fin r, if J i = x then (1 : ℕ) else 0) =
      (∑ i : Fin r, if K i = x then (1 : ℕ) else 0) +
        (∑ i : Fin r, if L i = x then (1 : ℕ) else 0)

private def balancedPluckerRatio {r n : ℕ}
    (M : Matrix (Fin r) (Fin n) ℝ)
    (I J K L : Fin r → Fin n) : ℝ :=
  maximalMinor M I * maximalMinor M J /
    (maximalMinor M K * maximalMinor M L)

/-- Claim 17843: positive completion scales every ordered maximal minor by the
product of the corresponding positive column scales, preserves the fixed
alternating chirotope, and cancels from every balanced Pluecker ratio.  The
positive gamma--Green completion is represented in the nonconfluent case by
this independent positive column scaling action. -/
def claim17843_nonconfluentPositiveCompletionProjectivelyTrivial : Prop :=
  ∀ (r n : ℕ) (M : Matrix (Fin r) (Fin n) ℝ) (scale : Fin n → ℝ),
    strictAlternating M →
      (∀ j, 0 < scale j) →
      strictAlternating (columnScale M scale) ∧
      (∀ I : Fin r → Fin n, Function.Injective I →
        maximalMinor (columnScale M scale) I =
          (∏ j : Fin r, scale (I j)) * maximalMinor M I) ∧
      sameChirotope M (columnScale M scale) ∧
      fixedChirotopeProjectivelyEquivalent M (columnScale M scale) ∧
      (∀ (I J K L : Fin r → Fin n),
        2 ≤ r →
        StrictMono I → StrictMono J → StrictMono K → StrictMono L →
        balancedColumnOccurrence I J K L →
        balancedPluckerRatio (columnScale M scale) I J K L =
          balancedPluckerRatio M I J K L)

end

end MathlibPlus.Open.ResearchFormalization.NonconfluentCompletionClaim17843
