import Mathlib

namespace MathlibPlus.Algebra.Claim23430

/-- The falling-monomial degree statement recorded in claim 23430. -/
theorem fallingMonomial_is_rational_polynomial
    (a b c : ℕ) (habc : a + b + c ≤ 3) :
    ∃ p : Polynomial ℚ,
      p.natDegree ≤ a + b ∧
      a + b ≤ 3 ∧
      ∀ t : ℚ,
        p.eval t =
          (descPochhammer ℚ a).eval (5 + t) *
            (descPochhammer ℚ b).eval (5 - t) *
              (descPochhammer ℚ c).eval 5 := by
  let p : Polynomial ℚ :=
    (descPochhammer ℚ a).comp (Polynomial.X + Polynomial.C 5) *
      (descPochhammer ℚ b).comp (Polynomial.C 5 - Polynomial.X) *
        Polynomial.C ((descPochhammer ℚ c).eval 5)
  refine ⟨p, ?_, by omega, ?_⟩
  · have hqa : (Polynomial.X + Polynomial.C (5 : ℚ)).natDegree ≤ 1 := by
      simpa using
        (Polynomial.natDegree_add_le (Polynomial.X : Polynomial ℚ)
          (Polynomial.C (5 : ℚ)))
    have hqb : (Polynomial.C (5 : ℚ) - Polynomial.X).natDegree ≤ 1 := by
      simpa [sub_eq_add_neg] using
        (Polynomial.natDegree_add_le (Polynomial.C (5 : ℚ))
          (-Polynomial.X : Polynomial ℚ))
    have hca :
        ((descPochhammer ℚ a).comp
          (Polynomial.X + Polynomial.C (5 : ℚ))).natDegree ≤ a := by
      calc
        _ ≤ (descPochhammer ℚ a).natDegree *
            (Polynomial.X + Polynomial.C (5 : ℚ)).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ a * 1 := by
          rw [descPochhammer_natDegree]
          exact Nat.mul_le_mul_left _ hqa
        _ = a := Nat.mul_one _
    have hcb :
        ((descPochhammer ℚ b).comp
          (Polynomial.C (5 : ℚ) - Polynomial.X)).natDegree ≤ b := by
      calc
        _ ≤ (descPochhammer ℚ b).natDegree *
            (Polynomial.C (5 : ℚ) - Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ b * 1 := by
          rw [descPochhammer_natDegree]
          exact Nat.mul_le_mul_left _ hqb
        _ = b := Nat.mul_one _
    dsimp [p]
    calc
      ((descPochhammer ℚ a).comp (Polynomial.X + Polynomial.C 5) *
          (descPochhammer ℚ b).comp (Polynomial.C 5 - Polynomial.X) *
          Polynomial.C ((descPochhammer ℚ c).eval 5)).natDegree ≤
        (((descPochhammer ℚ a).comp (Polynomial.X + Polynomial.C 5) *
          (descPochhammer ℚ b).comp (Polynomial.C 5 - Polynomial.X)).natDegree +
          (Polynomial.C ((descPochhammer ℚ c).eval 5)).natDegree) :=
        Polynomial.natDegree_mul_le
      _ ≤ (a + b) + 0 := by
        exact add_le_add
          (Polynomial.natDegree_mul_le.trans (add_le_add hca hcb))
          (by simp)
      _ = a + b := by simp
  · intro t
    dsimp [p]
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    congr 1
    rw [add_comm t 5]

end MathlibPlus.Algebra.Claim23430
