import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/-- Nonzero coordinate projections do not force a row space to be the whole
ambient two-coordinate space. -/
theorem claim17089_nonzeroProjectionsNotSpanning :
    let S : Submodule ℚ (Fin 2 → ℚ) :=
      { carrier := {x | x 0 = x 1}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Pi.add_apply, Pi.add_apply, hx, hy]
        smul_mem' := by
          intro a x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [Pi.smul_apply, Pi.smul_apply, hx] }
    (∀ i : Fin 2, ∃ x : Fin 2 → ℚ, x ∈ S ∧ x i ≠ 0) ∧
      ∃ y : Fin 2 → ℚ, y ∉ S := by
  dsimp
  constructor
  · intro i
    refine ⟨fun _ => 1, ?_, ?_⟩
    · change (1 : ℚ) = 1
      rfl
    · simp
  · refine ⟨![1, 0], ?_⟩
    change ¬ ((![1, 0] : Fin 2 → ℚ) 0 = (![1, 0] : Fin 2 → ℚ) 1)
    norm_num

end MathlibPlus.LinearAlgebra
