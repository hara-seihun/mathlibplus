import Mathlib

namespace MathlibPlus.Algebra.Claim46851

/--
The GSB/local-`h` equivalence, with the finite coefficient window and its
positivity hypotheses explicit.  The coefficients are otherwise arbitrary
positive reals, as in the source statement.
-/
theorem gsb_local_h_equivalence
    (α k : ℕ) (hk : k + 2 ≤ α) (a : ℕ → ℝ)
    (ha : ∀ i ≤ α, 0 < a i) :
    let μ : ℕ → ℝ := fun i => (i + 1 : ℝ) * a (i + 1) / a i
    let h : ℕ → ℝ := fun i => μ i - (i + 1 : ℝ)
    (((k + 2 : ℝ) * a k * a (k + 2) ≤
          (k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1)) ↔
        h (k + 1) ≤ h k) ∧
      (a (k + 1) ≥ a k ↔ h k ≥ 0) := by
  dsimp
  have hk_le : k ≤ α := by omega
  have hk1_le : k + 1 ≤ α := by omega
  have hak : 0 < a k := ha k hk_le
  have hak1 : 0 < a (k + 1) := ha (k + 1) hk1_le
  have hforward :
      ((k + 2 : ℝ) * a k * a (k + 2) ≤
          (k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1)) ↔
        (k + 2 : ℝ) * a (k + 2) / a (k + 1) - (k + 2 : ℝ) ≤
          (k + 1 : ℝ) * a (k + 1) / a k - (k + 1 : ℝ) := by
    constructor
    · intro hp
      have hp1 : (k + 2 : ℝ) * a (k + 2) ≤
          ((k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1)) / a k := by
        apply (le_div_iff₀ hak).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hp
      have hp2 : (k + 2 : ℝ) * a (k + 2) / a (k + 1) ≤
          (((k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1)) / a k) /
            a (k + 1) := by
        apply (div_le_iff₀ hak1).2
        calc
          (k + 2 : ℝ) * a (k + 2) ≤
              ((k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1)) / a k := hp1
          _ = (((k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1)) / a k) /
              a (k + 1) * a (k + 1) := by field_simp
      have hp3 : (k + 2 : ℝ) * a (k + 2) / a (k + 1) ≤
          (k + 1 : ℝ) * a (k + 1) / a k + 1 := by
        convert hp2 using 1 <;> field_simp
      linarith
    · intro hh
      have hh' : (k + 2 : ℝ) * a (k + 2) / a (k + 1) ≤
          (k + 1 : ℝ) * a (k + 1) / a k + 1 := by
        linarith
      have hh1 : (k + 2 : ℝ) * a (k + 2) ≤
          ((k + 1 : ℝ) * a (k + 1) / a k + 1) * a (k + 1) := by
        exact (div_le_iff₀ hak1).1 hh'
      have hh2 : (k + 2 : ℝ) * a (k + 2) * a k ≤
          ((k + 1 : ℝ) * a (k + 1) / a k + 1) * a (k + 1) * a k :=
        mul_le_mul_of_nonneg_right hh1 hak.le
      have hh3 : (k + 2 : ℝ) * a (k + 2) * a k ≤
          (k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1) := by
        calc
          (k + 2 : ℝ) * a (k + 2) * a k ≤
              ((k + 1 : ℝ) * a (k + 1) / a k + 1) * a (k + 1) * a k := hh2
          _ = (k + 1 : ℝ) * a (k + 1) ^ 2 + a k * a (k + 1) := by
            field_simp
      simpa [mul_assoc, mul_left_comm, mul_comm] using hh3
  constructor
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
    convert hforward using 1 <;> ring
  · have hfactor : (k + 1 : ℝ) * a (k + 1) / a k - (k + 1 : ℝ) =
        (k + 1 : ℝ) * (a (k + 1) - a k) / a k := by
      field_simp
    rw [hfactor]
    constructor
    · intro h
      exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h)) hak.le
    · intro h
      have hnum : 0 ≤ (k + 1 : ℝ) * (a (k + 1) - a k) := by
        have := (le_div_iff₀ hak).1 h
        simpa using this
      have hdiff : 0 ≤ a (k + 1) - a k :=
        (mul_nonneg_iff_of_pos_left (by positivity)).1 hnum
      exact sub_nonneg.mp hdiff

end MathlibPlus.Algebra.Claim46851
