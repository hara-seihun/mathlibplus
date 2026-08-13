import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim26940

/-- A nonzero three-term affine relation is exactly a nontrivial point on the
line through `A` and `B`.  The source uses rational coefficients, so the
scalar field is made explicit. -/
theorem affineLineCriterion
    {V : Type _} [AddCommGroup V] [Module ℚ V]
    (A B C : V) (_hnot : ¬ (A = B ∧ B = C)) :
    (∃ a b c : ℚ,
      a + b + c = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
        a • A + b • B + c • C = 0) ↔
      ∃ q : ℚ, q ≠ 0 ∧ q ≠ 1 ∧ C - A = q • (B - A) := by
  constructor
  · rintro ⟨a, b, c, habc, ha, hb, hc, hrel⟩
    refine ⟨-b / c, div_ne_zero (neg_ne_zero.mpr hb) hc, ?_, ?_⟩
    · intro hq
      have hbc : -b = c := by simpa using (div_eq_iff hc).mp hq
      apply ha
      linarith
    · have hrel' := congrArg (fun x : V => c⁻¹ • x) hrel
      have hrel'' : (a / c) • A + (b / c) • B + C = 0 := by
        simpa [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm,
          mul_assoc, mul_inv_cancel₀ hc] using hrel'
      have hac : a / c = -b / c - 1 := by
        apply (div_eq_iff hc).2
        field_simp [hc]
        linarith
      rw [hac] at hrel''
      let q : ℚ := -b / c
      have hqb : (-q : ℚ) = b / c := by
        dsimp [q]
        ring
      have hrelq : (q - 1) • A + (-q) • B + C = 0 := by
        rw [hqb]
        simpa [q, sub_eq_add_neg, add_smul, smul_add, neg_smul, add_assoc,
          add_comm, add_left_comm] using hrel''
      have hz : (C - A) - (q • (B - A)) = 0 := by
        simpa [sub_eq_add_neg, smul_sub, smul_add, neg_smul, add_smul,
          add_assoc, add_comm, add_left_comm] using hrelq
      exact sub_eq_zero.mp hz
  · rintro ⟨q, hq0, hq1, hline⟩
    refine ⟨q - 1, -q, 1, ?_, sub_ne_zero.mpr hq1, neg_ne_zero.mpr hq0,
      one_ne_zero, ?_⟩
    · ring
    · have hz : (C - A) - q • (B - A) = 0 := sub_eq_zero.mpr hline
      simpa [sub_eq_add_neg, sub_smul, smul_sub, smul_add, add_smul,
        neg_smul, add_assoc, add_comm, add_left_comm] using hz

end MathlibPlus.Algebra.Claim26940
