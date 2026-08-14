import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.BatchK0190

/-- The quantitative orbit-block assertion from admitted Claim 10052. -/
def quasiuniformIrrationalOrbitBlocks : Prop :=
  ∃ (c₀ C₀ : ℝ) (C : ℕ),
    0 < c₀ ∧ c₀ < C₀ ∧
      ∀ α : ℝ, Irrational α →
        ∀ B : ℕ, ∃ (N K : ℕ) (n : ℕ → ℕ) (u : ℕ → ℝ),
          B < K ∧
          Odd K ∧
          N ≤ K + C ∧ K ≤ N + C ∧
          n 0 = 0 ∧
          (∀ i : ℕ, i < K → i ≠ 0 → N ≤ n i ∧ n i < 2 * N) ∧
          (∀ i j : ℕ, i < K → j < K → i ≠ j → n i ≠ n j) ∧
          (∀ i : ℕ, i < K → u i = Int.fract ((n i : ℝ) * α)) ∧
          u 0 = 0 ∧
          (∀ i : ℕ, i < K → 0 ≤ u i ∧ u i < 1) ∧
          (∀ i : ℕ, i + 1 < K →
            u i < u (i + 1) ∧
              c₀ / (K : ℝ) ≤ u (i + 1) - u i ∧
              u (i + 1) - u i ≤ C₀ / (K : ℝ))

/-- Barycentric divided-difference weights for a finite list of nodes. -/
def barycentricWeight (K j : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∏ l ∈ (Finset.range K).erase j, (x j - x l)⁻¹

/-- The adjacent-gap and fixed-interval hypotheses for Claim 10054. -/
def QuasiuniformNodes
    (c₀ C₀ A B : ℝ) (K : ℕ) (x : ℕ → ℝ) : Prop :=
  1 ≤ K ∧
    0 < c₀ ∧ c₀ ≤ C₀ ∧ A ≤ B ∧
    (∀ i : ℕ, i < K → A ≤ x i ∧ x i ≤ B) ∧
    (∀ i : ℕ, i + 1 < K →
      c₀ / (K : ℝ) ≤ x (i + 1) - x i ∧
        x (i + 1) - x i ≤ C₀ / (K : ℝ))

/-- The barycentric coefficient envelope from admitted Claim 10054. -/
def barycentricCoefficientEnvelope : Prop :=
  ∃ (c₀ C₀ Cstar : ℝ),
    0 < c₀ ∧ c₀ ≤ C₀ ∧ 1 < Cstar ∧
      ∀ (K : ℕ) (A B : ℝ) (x : ℕ → ℝ),
        QuasiuniformNodes c₀ C₀ A B K x →
          ∀ j : ℕ, j < K →
            let d := fun i : ℕ => barycentricWeight K i x
            let a := fun i : ℕ => d i / d 0
            a 0 = 1 ∧ |a j| ≤ Cstar ^ K

end MathlibPlus.Open.Research.BatchK0190
