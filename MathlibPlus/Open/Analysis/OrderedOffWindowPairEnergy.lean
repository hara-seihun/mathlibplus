import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The ordered off-window spectral-pair energy, retaining every ordered pair
whose first or second index lies outside the central window. -/
def orderedOffWindowPairEnergy
    {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin r → ℝ)
    (W : Finset (Fin r))
    (_hA : ∀ i j, A i j = -A j i)
    (_hW : 2 ≤ W.card)
    (P_O_A : ℝ) : Prop :=
  let O : Finset (Fin r) := Wᶜ
  P_O_A =
    ∑ i : Fin r, (∑ j ∈ Finset.univ.filter
      (fun j => i ≠ j ∧ (i ∈ O ∨ j ∈ O)),
      ((V.transpose * A * V) i j) ^ 2 / (x i - x j) ^ 2)

end MathlibPlus.Open.Analysis
