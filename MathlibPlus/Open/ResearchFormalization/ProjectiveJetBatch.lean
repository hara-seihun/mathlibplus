import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ProjectiveJetBatch

noncomputable section

private def fourColumnMatrix (c₀ c₁ u z : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 4) ℝ :=
  fun i j => (![c₀, c₁, u, z] : Fin 4 → Fin 2 → ℝ) j i

private def rankTwoMinor {n : ℕ}
    (A : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  A 0 i * A 1 j - A 1 i * A 0 j

private def rankTwoCrossRatio (A : Matrix (Fin 2) (Fin 4) ℝ) : ℝ :=
  rankTwoMinor A 0 2 * rankTwoMinor A 1 3 /
    (rankTwoMinor A 0 1 * rankTwoMinor A 2 3)

private def firstOrderLeibnizShear (ρ : ℝ)
    (A : Matrix (Fin 2) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  fourColumnMatrix (fun i => A i 0)
    (fun i => A i 1 + ρ * A i 0)
    (fun i => A i 2) (fun i => A i 3)

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

private def sharpFourPointProfile
    (A : Matrix (Fin 2) (Fin 4) ℝ) : Prop :=
  rankTwoMinor A 0 1 * rankTwoMinor A 0 2 *
      rankTwoMinor A 0 3 * rankTwoMinor A 2 3 ≠ 0

/-- Claim 17852: after positive diagonal factors are removed, the first-order
Leibniz action at the double anchor is the indicated shear, and it shifts the
labeled balanced cross-ratio by the displayed minor expression. -/
def crossRatioShiftUnderFirstOrderLeibnizShear_claim17852 : Prop :=
  ∀ (c₀ c₁ u z : Fin 2 → ℝ) (q : ℝ → ℝ) (a : ℝ),
    let A := fourColumnMatrix c₀ c₁ u z
    let ρ := deriv q a / q a
    let qA := firstOrderLeibnizShear ρ A
    rankTwoCrossRatio qA - rankTwoCrossRatio A =
      ρ * rankTwoMinor A 0 2 * rankTwoMinor A 0 3 /
        (rankTwoMinor A 0 1 * rankTwoMinor A 2 3)

/-- Claim 17853: the four-vector sharp profile detects exactly the vanishing
of the first logarithmic derivative, while three labeled rank-two points have
no projective modulus. -/
def sharpFirstOrderMixingCriterion_claim17853 : Prop :=
  (∀ (A : Matrix (Fin 2) (Fin 4) ℝ) (q : ℝ → ℝ) (a : ℝ),
    sharpFourPointProfile A →
      (rankTwoProjectivelyEquivalent A
          (firstOrderLeibnizShear (deriv q a / q a) A) ↔
        deriv q a / q a = 0)) ∧
  (∀ A B : Matrix (Fin 2) (Fin 3) ℝ,
    threePointNondegenerate A → threePointNondegenerate B →
      rankTwoProjectivelyEquivalent A B) ∧
  (∃ A : Matrix (Fin 2) (Fin 4) ℝ, sharpFourPointProfile A)

private def gammaGreenFactor (s : ℝ) : ℝ :=
  s * (1 - s) * Real.pi ^ (-s / 2) * Real.Gamma (1 + s / 2)

private def gammaGreenJetCompletion
    (A : Matrix (Fin 2) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  firstOrderLeibnizShear
    (deriv gammaGreenFactor (1 / 2) / gammaGreenFactor (1 / 2)) A

private def osculatingLine (A : Matrix (Fin 2) (Fin 4) ℝ) :
    Submodule ℝ (Fin 2 → ℝ) :=
  Submodule.span ℝ {fun i => A i 0}

/-- Claim 17856: gamma--Green completion changes the labeled projective class
on every nondegenerate sharp jet profile at the central double anchor, while
preserving the associated osculating line in the two-dimensional vector space. -/
def gammaGreenCompletionNontrivialOnSharpJetProfile_claim17856 : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 4) ℝ,
    (∀ i j : Fin 4, i ≠ j → rankTwoMinor A i j ≠ 0) →
      rankTwoCrossRatio (gammaGreenJetCompletion A) ≠ rankTwoCrossRatio A ∧
        osculatingLine (gammaGreenJetCompletion A) = osculatingLine A

end

end MathlibPlus.Open.ResearchFormalization.ProjectiveJetBatch
