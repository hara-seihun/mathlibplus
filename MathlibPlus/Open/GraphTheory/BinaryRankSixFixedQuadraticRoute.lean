import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Exact ordinary undirected CI-defect census for the displayed fixed
quadratic permutation on `F₂⁶`: defects occur only in valencies 28 through 35,
with the stated binomial distribution, so the route's minimum is 28. -/
def binaryRankSixFixedQuadraticRouteDefectClassification : Prop :=
  let V := Fin 6 → ZMod 2
  let q : V → V := fun x =>
    ![
      x 0 + x 1 + x 0 * x 1 + x 2 + x 0 * x 2 + x 1 * x 2 + x 3 + x 4 + x 5,
      x 0 + x 0 * x 1 + x 0 * x 2 + x 3 + x 4,
      x 1 + x 0 * x 1 + x 1 * x 2 + x 3 + x 5,
      x 0 * x 1 + x 3,
      x 2 + x 0 * x 2 + x 1 * x 2 + x 4 + x 5,
      x 0 * x 2 + x 4]
  let isDefect : Set V → Prop := fun S =>
    0 ∉ S ∧
    (∀ x, x ∈ S ↔ -x ∈ S) ∧
    0 ∉ q '' S ∧
    (∀ x, x ∈ q '' S ↔ -x ∈ q '' S) ∧
    (∀ x y, y - x ∈ S ↔ q y - q x ∈ q '' S) ∧
    ¬ ∃ α : V ≃+ V, α '' S = q '' S
  Function.Bijective q ∧ q 0 = 0 ∧
    IsLeast {k : ℕ | ∃ S : Set V, isDefect S ∧ Set.ncard S = k} 28 ∧
    (∀ k : ℕ,
      Nat.card {S : Set V // isDefect S ∧ Set.ncard S = k} =
        if 28 ≤ k ∧ k ≤ 35 then 128 * Nat.choose 7 (k - 28) else 0)

end MathlibPlus.Open.GraphTheory
