import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-!
Formalization of admitted claim 47276 (R-2833).  The tail `T N` is written using
its canonical `Nat` reindexing `j ↦ j + (N + 1)`; thus it is exactly the sum over
indices `j > N`, without introducing a convergence hypothesis as an extra
assumption.
-/

/-- The dyadic tail identity, its one-step recurrence, and strict overlap. -/
theorem dyadicTailIdentity :
    let w : ℕ → ℝ := fun j => (j : ℝ) / (2 : ℝ) ^ j
    let T : ℕ → ℝ := fun N => ∑' j : ℕ, w (j + (N + 1))
    ∀ N : ℕ,
      T N = (N + 2 : ℝ) / (2 : ℝ) ^ N ∧
      T N = w (N + 1) + T (N + 1) ∧
      w (N + 1) < T (N + 1) := by
  dsimp
  have hformula : ∀ N : ℕ,
      (∑' j : ℕ, ((j + (N + 1) : ℕ) : ℝ) / (2 : ℝ) ^ (j + (N + 1))) =
        (N + 2 : ℝ) / (2 : ℝ) ^ N := by
    intro N
    let q : ℝ := 1 / 2
    have hq : ‖q‖ < 1 := by
      dsimp [q]
      norm_num [Real.norm_eq_abs]
    have hgeom : HasSum (fun j : ℕ => q ^ j) 2 := by
      simpa [q] using (hasSum_geometric_two)
    have hlinear : HasSum (fun j : ℕ => (j : ℝ) * q ^ j) 2 := by
      have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := q) hq
      convert h using 1
      · rfl
      · dsimp [q]
        norm_num [Real.norm_eq_abs]
    have hscaled : HasSum (fun j : ℕ => (N + 1 : ℝ) * q ^ j)
        ((N + 1 : ℝ) * 2) := hgeom.mul_left _
    have hadd : HasSum (fun j : ℕ => ((j : ℝ) + (N + 1 : ℝ)) * q ^ j)
        (2 + (N + 1 : ℝ) * 2) := by
      have h := hlinear.add hscaled
      convert h using 1
      funext j
      ring
    have htail : HasSum
        (fun j : ℕ => ((j + (N + 1) : ℕ) : ℝ) * q ^ (j + (N + 1)))
        (q ^ (N + 1) * (2 + (N + 1 : ℝ) * 2)) := by
      have h := hadd.mul_left (q ^ (N + 1))
      convert h using 1 <;> try rfl
      funext j
      simp only [Nat.cast_add, Nat.cast_one, pow_add]
      ring
    have htail' : HasSum
        (fun j : ℕ => ((j + (N + 1) : ℕ) : ℝ) / (2 : ℝ) ^ (j + (N + 1)))
        (q ^ (N + 1) * (2 + (N + 1 : ℝ) * 2)) := by
      convert htail using 1
      funext j
      dsimp [q]
      rw [one_div_pow]
      field_simp
    rw [htail'.tsum_eq]
    dsimp [q]
    norm_num [div_pow]
    ring
  intro N
  have hN := hformula N
  refine ⟨hN, ?_, ?_⟩
  · rw [hN, hformula (N + 1)]
    field_simp
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  · rw [hformula (N + 1)]
    apply (div_lt_div_iff_of_pos_right
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (N + 1))).2
    norm_num [Nat.cast_add, Nat.cast_one]

end MathlibPlus.Analysis
