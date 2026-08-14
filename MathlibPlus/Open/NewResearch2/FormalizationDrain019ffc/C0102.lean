import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain019ffc
namespace C0102

/-- Claim 1572: the one-column word, explicit matching, endpoint partners,
and signed alternating coordinate identity are retained. -/
def claim1572
    (d n : ℕ)
    (word : List (Fin 2))
    (matching : Set (ℕ × ℕ))
    (partners : Set ℕ)
    (incidence : ℕ → ℤ)
    (alpha H : Fin (n + 1) → ℝ) : Prop :=
  1 ≤ n ∧ n ≤ d ∧
    word =
      List.replicate (d - n + 1) (0 : Fin 2) ++
        [1] ++ List.replicate n (0 : Fin 2) ++ List.replicate d (1 : Fin 2) ∧
    matching =
      {p : ℕ × ℕ |
        (∃ i : ℕ, i < d - n ∧ p = (i, 2 * d + 1 - i)) ∨
          p = (d - n, d - n + 1) ∨
          (∃ i : ℕ, d - n + 2 ≤ i ∧ i ≤ d + 1 ∧
            p = (i, 2 * d + 3 - i))} ∧
    partners = {n, n - 1} ∧
    incidence n = 1 ∧ incidence (n - 1) = -1 ∧
    (-alpha ⟨n - 1, by omega⟩ + alpha ⟨n, by omega⟩ =
      (-1 : ℝ) ^ n * H ⟨n, by omega⟩) ∧
    alpha ⟨n, by omega⟩ =
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ j.1 * H j

end C0102
end MathlibPlus.Open.NewResearch2.FormalizationDrain019ffc
