import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim32617

/-- The symmetric `5 × 5` matrices over `𝔽₃` form a 15-dimensional
space, and hence there are exactly `3^15` of them. -/
theorem symmetricMatrixDimensionAndCard_claim32617 :
    ∃ Sym : Submodule (ZMod 3) (Matrix (Fin 5) (Fin 5) (ZMod 3)),
      (∀ M, M ∈ Sym ↔ M.IsSymm) ∧
        Module.finrank (ZMod 3) Sym = 15 ∧
        Nat.card Sym = 3 ^ 15 := by
  let Sym : Submodule (ZMod 3) (Matrix (Fin 5) (Fin 5) (ZMod 3)) :=
    { carrier := {M | M.IsSymm}
      zero_mem' := by
        apply Matrix.IsSymm.ext
        intro i j
        simp
      add_mem' := by
        intro A B hA hB
        apply Matrix.IsSymm.ext
        intro i j
        have hA' : A j i = A i j := by
          simpa [Matrix.transpose_apply] using congrFun (congrFun hA.eq i) j
        have hB' : B j i = B i j := by
          simpa [Matrix.transpose_apply] using congrFun (congrFun hB.eq i) j
        simp only [Matrix.add_apply]
        rw [hA', hB']
      smul_mem' := by
        intro c A hA
        apply Matrix.IsSymm.ext
        intro i j
        have hA' : A j i = A i j := by
          simpa [Matrix.transpose_apply] using congrFun (congrFun hA.eq i) j
        simp only [smul_eq_mul, Matrix.smul_apply]
        rw [hA'] }
  let U := {p : Fin 5 × Fin 5 // p.1 ≤ p.2}
  let e : Sym ≃ₗ[ZMod 3] (U → ZMod 3) :=
    { toFun := fun M p => M.1 p.1.1 p.1.2
      invFun := fun f =>
        ⟨fun i j => f ⟨(min i j, max i j), min_le_max⟩, by
          apply Matrix.IsSymm.ext
          intro i j
          simp [min_comm, max_comm]⟩
      left_inv := by
        intro M
        apply Subtype.ext
        funext i j
        by_cases h : i ≤ j
        · simp [U, min_eq_left h, max_eq_right h]
        · have h' : j ≤ i := le_of_lt (lt_of_not_ge h)
          have hs : M.1 j i = M.1 i j := by
            simpa [Matrix.transpose_apply] using congrFun (congrFun M.2.eq i) j
          simp [U, min_eq_right h', max_eq_left h', hs]
      right_inv := by
        intro f
        funext p
        simp [U, min_eq_left p.2, max_eq_right p.2]
      map_add' := by
        intro A B
        rfl
      map_smul' := by
        intro c A
        rfl }
  have hU : Fintype.card U = 15 := by
    rw [Fintype.card_subtype]
    native_decide
  refine ⟨Sym, (by intro M; rfl), ?_, ?_⟩
  · rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card]
    exact hU
  · rw [Nat.card_congr e.toEquiv, Nat.card_fun]
    norm_num [hU]

end MathlibPlus.LinearAlgebra.Claim32617
