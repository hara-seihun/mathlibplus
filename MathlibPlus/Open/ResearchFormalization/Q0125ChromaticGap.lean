import MathlibPlus.Open.Probability.RandomGraphBatch
import MathlibPlus.Combinatorics.Claim16692

namespace MathlibPlus.Open.ResearchFormalization.Q0125ChromaticGap

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq
open MathlibPlus.Open.Probability.FormalizationBatch
open MathlibPlus.Combinatorics

/-- The exact finite-graph event for the chromatic/cochromatic gap. -/
def gapAtMost (g : ℕ → ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ((G.chromaticNumber.toNat : ℝ) -
      (cochromaticNumber_claim16692 G : ℝ)) ≤ g n

def gapAtMostConstant (M : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ((G.chromaticNumber.toNat : ℝ) -
      (cochromaticNumber_claim16692 G : ℝ)) ≤ M

def uniformGraphProbability {n : ℕ} (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Fintype.card {G : SimpleGraph (Fin n) // E G} : ℝ) /
    (Fintype.card (SimpleGraph (Fin n)) : ℝ)

def gapProbability (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  uniformGraphProbability (gapAtMost g n)

def lowerScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log (Real.log (n : ℝ))) /
    (Real.log (n : ℝ)) ^ 3

def boundedInProbability : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      uniformGraphProbability (gapAtMostConstant M n) > 1 - ε

/-- Claim 16697: a uniformly `0.999`-likely proposed bound forces an
unbounded subsequence at the displayed scale, and the gap is not bounded in
probability. -/
def claim16697_gapNotBoundedInProbability : Prop :=
  ∀ g : ℕ → ℝ,
    (∀ n : ℕ, gapProbability g n > (999 : ℝ) / 1000) →
      ∃ c : ℝ, 0 < c ∧
        (∀ B : ℕ, ∃ n : ℕ, B < n ∧ g n > c * lowerScale n) ∧
        ¬ boundedInProbability

end

end MathlibPlus.Open.ResearchFormalization.Q0125ChromaticGap
