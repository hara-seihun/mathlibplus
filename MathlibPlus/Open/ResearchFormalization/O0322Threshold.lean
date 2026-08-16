import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0322

noncomputable section

open scoped BigOperators
open Filter
open MeasureTheory
open Set
open Topology

/-- The parameter-two generalized Laguerre polynomial in the admitted
normalization. -/
noncomputable def laguerreTwo (d : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℝ) ^ k * (Nat.choose (d + 2) (d - k) : ℝ) * t ^ k /
      (Nat.factorial k : ℝ)

/-- The exact Laplace--Laguerre transform `I_d(δ)`. -/
noncomputable def laplaceLaguerre (d : ℕ) (δ : ℝ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), Real.exp (-δ * t) * laguerreTwo d t

/-- The fixed mode ratio `r_δ`. -/
def poleRatio (δ : ℝ) : ℝ :=
  -(1 - δ) / δ

/-- Claim 15363: the ratio `r_δ` gives the exact one-half threshold,
with eventual magnitude/sign semantics and a decaying post-threshold residual. -/
def claim15363 : Prop :=
  ∀ δ : ℝ, 0 < δ →
    let rδ : ℝ := poleRatio δ
    let I : ℕ → ℝ := fun d => laplaceLaguerre d δ
    ((δ < 1 / 2 →
        |rδ| > 1 ∧
          ∃ c : ℝ, 0 < c ∧
            ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              c * ((1 - δ) / δ) ^ d ≤ |I d| ∧
                0 < (-1 : ℝ) ^ d * I d) ∧
      (δ = 1 / 2 →
        ∀ d : ℕ, I d = d + 3 / 2 + (-1 : ℝ) ^ d / 2) ∧
      (δ > 1 / 2 →
        |rδ| < 1 ∧
          (∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ d : ℕ in atTop,
              |I d - ((d : ℝ) + 2 - δ)| ≤ C * |rδ| ^ d) ∧
          Tendsto
            (fun d : ℕ => I d - ((d : ℝ) + 2 - δ))
            atTop (𝓝 0)))

end

end MathlibPlus.Open.ResearchFormalization.O0322
