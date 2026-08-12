import Mathlib

namespace MathlibPlus.Analysis

/-- The cyclic target functional from claim 47785, with zero-based finite
coordinates.  A shift argument `j : Fin n` itself enforces that the cyclic
modulus is nonzero. -/
def cyclicTarget_claim47785
    {n : ℕ} (a O : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ r : Fin n, a r * O (r + j)

/-- Positive coefficients summing to one and bounded inputs produce cyclic
weighted targets in the exact interval `[-1,1]`. -/
theorem claim47785_cyclic_bounded_target
    {n : ℕ} (a O : Fin n → ℝ) (j : Fin n)
    (ha : ∀ r, 0 < a r)
    (ha_sum : ∑ r : Fin n, a r = 1)
    (hO : ∀ r, -1 ≤ O r ∧ O r ≤ 1) :
    -1 ≤ cyclicTarget_claim47785 a O j ∧
      cyclicTarget_claim47785 a O j ≤ 1 := by
  have hnonneg : ∀ r : Fin n, 0 ≤ a r := fun r => (ha r).le
  have hlow : ∀ r : Fin n,
      -a r ≤ a r * O (r + j) := by
    intro r
    have h := (hO (r + j)).1
    have hm := mul_le_mul_of_nonneg_left h (hnonneg r)
    simpa [mul_neg] using hm
  have hupp : ∀ r : Fin n,
      a r * O (r + j) ≤ a r := by
    intro r
    have h := (hO (r + j)).2
    have hm := mul_le_mul_of_nonneg_left h (hnonneg r)
    simpa using hm
  constructor
  · calc
      (-1 : ℝ) = ∑ r : Fin n, -a r := by simp [ha_sum]
      _ ≤ ∑ r : Fin n, a r * O (r + j) :=
        Finset.sum_le_sum (fun r _ => hlow r)
      _ = cyclicTarget_claim47785 a O j := rfl
  · calc
      cyclicTarget_claim47785 a O j =
          ∑ r : Fin n, a r * O (r + j) := rfl
      _ ≤ ∑ r : Fin n, a r := Finset.sum_le_sum (fun r _ => hupp r)
      _ = 1 := ha_sum

end MathlibPlus.Analysis
