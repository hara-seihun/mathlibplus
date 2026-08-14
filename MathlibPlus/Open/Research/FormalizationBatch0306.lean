import Mathlib

open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.Research

noncomputable def poissonWeight (x : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-x) * x ^ m / (Nat.factorial m : ℝ)

noncomputable def generalizedLaguerreTwo (n : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k * (Nat.choose (n + 2) (n - k) : ℝ) * z ^ k /
      (Nat.factorial k : ℝ)

noncomputable def laguerreAtom (m : ℕ) (z : ℝ) : ℝ :=
  if m < 2 then 0 else generalizedLaguerreTwo (m - 2) z

noncomputable def diagonalContinuation (x z : ℝ) : ℝ :=
  ∑' m : ℕ, poissonWeight x m *
    (laguerreAtom m z ^ 2 + laguerreAtom (m + 1) z ^ 2)

noncomputable def diagonal (x t : ℝ) : ℝ := diagonalContinuation x t

noncomputable def unshiftedGramTerm (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  poissonWeight x n * laguerreAtom n t ^ 2

noncomputable def onceShiftedGramTerm (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  poissonWeight x n * ((n : ℝ) / x) * laguerreAtom n t ^ 2

noncomputable def firstShiftGramTerm (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  poissonWeight x n * (1 + (n : ℝ) / x) * laguerreAtom n t ^ 2

noncomputable def unshiftedGraphDiagonal (x t : ℝ) : ℝ :=
  ∑' n : ℕ, unshiftedGramTerm x n t

noncomputable def onceShiftedGraphDiagonal (x t : ℝ) : ℝ :=
  ∑' n : ℕ, onceShiftedGramTerm x n t

noncomputable def firstShiftGraphDiagonal (x t : ℝ) : ℝ :=
  ∑' n : ℕ, firstShiftGramTerm x n t

def firstShiftIndexIdentity : Prop :=
  ∀ x : ℝ, 0 < x →
    (∀ n : ℕ, 1 ≤ n →
      poissonWeight x (n - 1) =
        (n : ℝ) / x * poissonWeight x n) ∧
    (∀ n : ℕ,
      poissonWeight x n +
          (if n = 0 then 0 else poissonWeight x (n - 1)) =
        poissonWeight x n * (1 + (n : ℝ) / x)) ∧
    (∀ n : ℕ, 0 < 1 + (n : ℝ) / x) ∧
    (∀ n : ℕ, 0 ≤ poissonWeight x n * ((n : ℝ) / x)) ∧
    (∀ n : ℕ, ∀ t : ℝ,
      unshiftedGramTerm x n t + onceShiftedGramTerm x n t =
        firstShiftGramTerm x n t) ∧
    (∀ n : ℕ, ∀ t : ℝ,
      0 ≤ unshiftedGramTerm x n t ∧
      0 ≤ onceShiftedGramTerm x n t) ∧
    (∀ t : ℝ,
      diagonal x t = firstShiftGraphDiagonal x t ∧
      0 ≤ unshiftedGraphDiagonal x t ∧
      0 ≤ onceShiftedGraphDiagonal x t ∧
      unshiftedGraphDiagonal x t + onceShiftedGraphDiagonal x t =
        firstShiftGraphDiagonal x t) ∧
    Tendsto
      (fun n : ℕ =>
        Real.log (1 + (n : ℝ) / x) / (n : ℝ))
      atTop (𝓝 0)

def matchingRealAxisLowerBound : Prop :=
  ∀ x : ℝ, 0 < x →
    (∀ t : ℝ, 0 < t → 0 < diagonal x t) ∧
    (fun t : ℝ =>
        Real.log (diagonal x t)
          - 3 * x ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ)
          + 2 * x ^ (2 / 3 : ℝ) * t ^ (1 / 3 : ℝ))
      =O[atTop]
        (fun t : ℝ => Real.log t) ∧
    (∀ J : Set ℝ, IsCompact J →
      ∃ L : ℝ → ℝ,
        (∀ᶠ T : ℝ in atTop,
          0 < L T ∧
            ∀ u ∈ J,
              diagonal x (T + u * T ^ (2 / 3 : ℝ)) ≥ L T) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ T : ℝ in atTop,
            3 * x ^ (1 / 3 : ℝ) * T ^ (2 / 3 : ℝ)
                - C * (T ^ (1 / 3 : ℝ) + Real.log T)
              ≤ Real.log (L T))

end MathlibPlus.Open.Research
