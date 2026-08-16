import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.SignCompression

/-- Claim 60211: finite-image functions admit the explicit ordered sign-row
compression, and every finite positive-support sign law has finite image of
size at most the number of sign patterns. -/
def finite_image_sign_row_compression : Prop :=
  (∀ (X : Type) (_ : Nonempty X) (f : X → ℝ),
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) →
    Set.Finite (Set.range f) →
    ∃ (m : ℕ) (a : ℕ → ℝ),
      0 < m ∧
      (∀ i, i < m → -1 ≤ a i ∧ a i ≤ 1) ∧
      (∀ i j, i < m → j < m → i < j → a i < a j) ∧
      Set.range f = {r | ∃ k, k < m ∧ r = a k} ∧
      ∃ (R : Fin (m + 1) → X → ℝ) (w : Fin (m + 1) → ℝ),
        (∀ j x, R j x = -1 ∨ R j x = 1) ∧
        (∀ x k, k < m → f x = a k →
          ∀ j, R j x = if j.1 ≤ k then 1 else -1) ∧
        (∀ j, w j =
          if j.1 = 0 then
            (1 + a 0) / 2
          else if j.1 = m then
            (1 - a (m - 1)) / 2
          else
            (a j.1 - a (j.1 - 1)) / 2) ∧
        (∀ j, 0 ≤ w j) ∧
        (∑ j, w j = 1) ∧
        (∀ x, ∑ j, w j * R j x = f x) ∧
        (∀ i j, i.1 ≤ j.1 → ∀ x, R j x = 1 → R i x = 1) ∧
        Set.ncard {j : Fin (m + 1) | w j ≠ 0} =
          (m - 1) +
            (if a 0 > -1 then 1 else 0) +
            (if a (m - 1) < 1 then 1 else 0) ∧
        Set.ncard {j : Fin (m + 1) | w j ≠ 0} ≤ m + 1) ∧
  (∀ (X : Type) (_ : Nonempty X) (s : ℕ)
      (R : Fin s → X → ℝ) (w : Fin s → ℝ),
    (∀ i x, R i x = -1 ∨ R i x = 1) →
    (∀ i, 0 < w i) →
    (∑ i, w i = 1) →
    let μ : X → ℝ := fun x => ∑ i, w i * R i x
    (∀ x, -1 ≤ μ x ∧ μ x ≤ 1) ∧
      Set.Finite (Set.range μ) ∧
      Set.ncard (Set.range μ) ≤ 2 ^ s)

end MathlibPlus.Open.FormalizationBatch.SignCompression
