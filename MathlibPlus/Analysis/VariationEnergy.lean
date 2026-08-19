import Mathlib

namespace MathlibPlus.Analysis.VariationEnergy

/-!
The K-0105 square-root lift uses `r` for even-indexed coefficients and `s`
for odd-indexed coefficients. -/

/-- The signed source reconstructs the boundary stagger and adjacent variation
energy on every finite index interval. -/
theorem signedSourceVariationEnergy_claim8610
    {R : Type*} [Field R] [CharZero R]
    (r s : ℕ → R) (A B : ℕ) (hAB : A ≤ B) :
    let U : ℕ → R := fun k => s k ^ 2 - r (k - 1) ^ 2
    let E : ℕ → R := fun k =>
      (s k - r (k - 1)) ^ 2 + (r k - s (k + 1)) ^ 2
    let S : ℕ → R := fun k =>
      s k * (s k - r (k - 1)) + r k * (r k - s (k + 1))
    let V : ℕ → ℕ → R := fun lo hi => (∑ k ∈ Finset.Icc lo hi, E k)
    (∑ k ∈ Finset.Icc A B, S k = (U A - U (B + 1)) / 2 + V A B / 2) ∧
      V A B = 2 * (∑ k ∈ Finset.Icc A B, S k) - U A + U (B + 1) := by
  let U : ℕ → R := fun k => s k ^ 2 - r (k - 1) ^ 2
  let E : ℕ → R := fun k =>
    (s k - r (k - 1)) ^ 2 + (r k - s (k + 1)) ^ 2
  let S : ℕ → R := fun k =>
    s k * (s k - r (k - 1)) + r k * (r k - s (k + 1))
  change
    (∑ k ∈ Finset.Icc A B, S k = (U A - U (B + 1)) / 2 +
      (∑ k ∈ Finset.Icc A B, E k) / 2) ∧
      (∑ k ∈ Finset.Icc A B, E k) =
        2 * (∑ k ∈ Finset.Icc A B, S k) - U A + U (B + 1)
  have hsource : ∀ k : ℕ, S k = (U k - U (k + 1)) / 2 + E k / 2 := by
    intro k
    dsimp [S, U, E]
    ring
  have htel :
      (∑ k ∈ Finset.Icc A B, (U k - U (k + 1))) = U A - U (B + 1) := by
    have hIcc : Finset.Icc A B = Finset.Ico A (B + 1) := by
      ext k
      simp
    rw [hIcc, Finset.sum_Ico_eq_sub _ (Nat.le_succ_of_le hAB)]
    rw [Finset.sum_range_sub']
    rw [Finset.sum_range_sub']
    ring
  have hmain :
      (∑ k ∈ Finset.Icc A B,
        ((U k - U (k + 1)) / 2 + E k / 2)) =
        (U A - U (B + 1)) / 2 +
          (∑ k ∈ Finset.Icc A B, E k) / 2 := by
    rw [Finset.sum_add_distrib]
    rw [← Finset.sum_div]
    rw [← Finset.sum_div]
    rw [htel]
  constructor
  · simpa only [hsource] using hmain
  · simp_rw [hsource]
    rw [hmain]
    ring

end MathlibPlus.Analysis.VariationEnergy
