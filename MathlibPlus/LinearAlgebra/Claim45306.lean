import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra

/--
The explicit adjacent-flag matrix in claim 45306 is the three-by-three
all-ones matrix.  Its rank over `ℚ` is one, while its determinant vanishes.
The source-specific identification of rows and columns with flags in
`F₂²` is recorded in the alignment note; this theorem captures the displayed
matrix invariant exactly.
-/
theorem adjacentFlagIncidenceMatrix_rank_one_claim45306 :
    let A : Matrix (Fin 3) (Fin 3) ℚ := fun _ _ => 1
    A.rank = 1 ∧ A.det = 0 := by
  dsimp
  let A : Matrix (Fin 3) (Fin 3) ℚ := fun _ _ => 1
  have hvec : A = Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℚ)) (fun _ : Fin 3 => (1 : ℚ)) := by
    ext i j
    simp [A, Matrix.vecMulVec]
  have hle : A.rank ≤ 1 := by
    rw [hvec]
    exact Matrix.rank_vecMulVec_le _ _
  have hne : A.rank ≠ 0 := by
    intro hz
    have hspan : Module.finrank ℚ (Submodule.span ℚ (Set.range A.col)) = 0 := by
      rw [← Matrix.rank_eq_finrank_span_cols]
      exact hz
    have hbot : Submodule.span ℚ (Set.range A.col) = ⊥ :=
      (Submodule.finrank_eq_zero).mp hspan
    have hmem : A.col 0 ∈ Submodule.span ℚ (Set.range A.col) :=
      Submodule.subset_span (Set.mem_range.2 ⟨0, rfl⟩)
    have hzero : A.col 0 = 0 := by
      have : A.col 0 ∈ (⊥ : Submodule ℚ (Fin 3 → ℚ)) := hbot ▸ hmem
      simpa using this
    have hnonzero : A.col 0 ≠ 0 := by
      intro h
      have h' := congrFun h (0 : Fin 3)
      change (1 : ℚ) = 0 at h'
      norm_num at h'
    exact hnonzero hzero
  have hrank : A.rank = 1 := by omega
  constructor
  · exact hrank
  · apply Matrix.det_zero_of_row_eq (show (0 : Fin 3) ≠ 1 by decide)
    funext j
    simp

end MathlibPlus.LinearAlgebra
