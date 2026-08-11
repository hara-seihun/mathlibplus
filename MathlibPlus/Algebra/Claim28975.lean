import Mathlib

namespace MathlibPlus.Algebra

/--
An integral point on a rational affine line with primitive integral direction
has a unique integral affine coordinate.
-/
theorem claim28975_unique_integer_affine_coordinate
    {n : ℕ} (Q₀ Q D : Fin n → ℤ) (t : ℚ)
    (hprimitive : ∃ a : Fin n → ℤ, ∑ j : Fin n, a j * D j = 1)
    (hline : ∀ j : Fin n,
      (Q j : ℚ) = (Q₀ j : ℚ) + t * (D j : ℚ)) :
    ∃! c : ℤ, ∀ j : Fin n, Q j = Q₀ j + c * D j := by
  obtain ⟨a, ha⟩ := hprimitive
  have hdiffQ : ∀ j : Fin n,
      ((Q j - Q₀ j : ℤ) : ℚ) = t * (D j : ℚ) := by
    intro j
    calc
      ((Q j - Q₀ j : ℤ) : ℚ) = (Q j : ℚ) - (Q₀ j : ℚ) := by
        norm_num
      _ = t * (D j : ℚ) := by rw [hline j]; ring
  let c : ℤ := ∑ j : Fin n, a j * (Q j - Q₀ j)
  have hbezoutQ : ∑ j : Fin n, (a j : ℚ) * (D j : ℚ) = 1 := by
    exact_mod_cast ha
  have hcoord : (c : ℚ) = t := by
    dsimp [c]
    rw [Int.cast_sum]
    calc
      (∑ j : Fin n, ((a j * (Q j - Q₀ j) : ℤ) : ℚ)) =
          ∑ j : Fin n, (a j : ℚ) * (t * (D j : ℚ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Int.cast_mul, hdiffQ]
      _ = ∑ j : Fin n, t * ((a j : ℚ) * (D j : ℚ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = t * ∑ j : Fin n, (a j : ℚ) * (D j : ℚ) := by
        rw [Finset.mul_sum]
      _ = t := by rw [hbezoutQ]; ring
  refine ⟨c, ?_, ?_⟩
  · intro j
    have hrat : (Q j : ℚ) = (Q₀ j : ℚ) + (c : ℚ) * (D j : ℚ) := by
      rw [hcoord]
      exact hline j
    exact_mod_cast hrat
  · intro c' hc'
    have hdiffC' : ∀ j : Fin n, Q j - Q₀ j = c' * D j := by
      intro j
      rw [hc' j]
      ring
    have hsumC' : c = c' := by
      dsimp [c]
      calc
        (∑ j : Fin n, a j * (Q j - Q₀ j)) =
            ∑ j : Fin n, a j * (c' * D j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hdiffC' j]
        _ = ∑ j : Fin n, c' * (a j * D j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = c' * ∑ j : Fin n, a j * D j := by
          rw [Finset.mul_sum]
        _ = c' := by rw [ha]; ring
    exact hsumC'.symm

end MathlibPlus.Algebra
