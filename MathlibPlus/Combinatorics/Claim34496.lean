import Mathlib

/-!
# Canonical fully frustrated cube signing

The source claim identifies cube vertices with subsets and assigns an edge in
coordinate `k` the sign `(-1) ^ |X ∩ [k-1]|`.  The theorem below writes one
coordinate square with `i < j` explicitly; every unordered pair of distinct
coordinates has such an ordering.
-/
namespace MathlibPlus.Combinatorics

/-- The product of the four canonical signs around every coordinate square is
`-1`.  Subsets of `[n]` are represented by finsets of `Fin n`. -/
theorem claim34496_frustrated_coordinate_square
    {n : ℕ} (X : Finset (Fin n)) (i j : Fin n)
    (hij : i < j) (hi : i ∉ X) (hj : j ∉ X) :
    let σ : Finset (Fin n) → Fin n → ℤ :=
      fun Y k => (-1 : ℤ) ^ (Y.filter (fun l => l < k)).card
    σ X i * σ (insert i X) j * σ (insert j X) i * σ X j = -1 := by
  dsimp
  have hcard_ij : ((insert i X).filter (fun l => l < j)).card =
      (X.filter (fun l => l < j)).card + 1 := by
    rw [Finset.filter_insert]
    have hif : i ∉ X.filter (fun l => l < j) := by simp [hi]
    simp only [hij, ↓reduceIte]
    rw [← Finset.cons_eq_insert i (X.filter (fun l => l < j)) hif,
      Finset.card_cons]
  have hji : ¬ j < i := not_lt_of_ge (le_of_lt hij)
  have hcard_ji : ((insert j X).filter (fun l => l < i)).card =
      (X.filter (fun l => l < i)).card := by
    rw [Finset.filter_insert]
    simp [hji]
  rw [hcard_ij, hcard_ji]
  calc
    (-1 : ℤ) ^ (X.filter (fun l => l < i)).card *
          (-1 : ℤ) ^ ((X.filter (fun l => l < j)).card + 1) *
          (-1 : ℤ) ^ (X.filter (fun l => l < i)).card *
          (-1 : ℤ) ^ (X.filter (fun l => l < j)).card =
        ((-1 : ℤ) ^ (X.filter (fun l => l < i)).card *
          (-1 : ℤ) ^ (X.filter (fun l => l < i)).card) *
        ((-1 : ℤ) ^ ((X.filter (fun l => l < j)).card + 1) *
          (-1 : ℤ) ^ (X.filter (fun l => l < j)).card) := by ring
    _ = (-1 : ℤ) ^ ((X.filter (fun l => l < i)).card +
          (X.filter (fun l => l < i)).card) *
        (-1 : ℤ) ^ ((X.filter (fun l => l < j)).card + 1 +
          (X.filter (fun l => l < j)).card) := by
      rw [← pow_add, ← pow_add]
    _ = -1 := by
      simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      rw [show (X.filter (fun l => l < i)).card +
          (X.filter (fun l => l < i)).card =
            (X.filter (fun l => l < i)).card * 2 by omega]
      rw [show 1 + ((X.filter (fun l => l < j)).card +
          (X.filter (fun l => l < j)).card) =
            (X.filter (fun l => l < j)).card * 2 + 1 by omega]
      rw [pow_add]
      have h_even (k : ℕ) : (-1 : ℤ) ^ (k * 2) = 1 := by
        rw [pow_mul]
        rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> norm_num
      rw [h_even, h_even]
      norm_num

end MathlibPlus.Combinatorics
