import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 4959. A square matrix over a field has full column rank exactly when its
determinant is nonzero.
-/
theorem fullColumnRank_iff_det_ne_zero_claim4959
    {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    A.rank = n ↔ A.det ≠ 0 := by
  constructor
  · intro hrank hdet
    obtain ⟨v, hv, hvzero⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := A)).2 hdet
    have hvker : v ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker]
      simpa [Matrix.mulVecLin_apply] using hvzero
    have hker_ne : LinearMap.ker A.mulVecLin ≠ (⊥ : Submodule K (Fin n → K)) := by
      intro hbot
      have hvbot : v ∈ (⊥ : Submodule K (Fin n → K)) := hbot ▸ hvker
      exact hv (by simpa using hvbot)
    have hker_pos : 0 < Module.finrank K (LinearMap.ker A.mulVecLin) :=
      lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.mpr hker_ne)
    have hrange : Module.finrank K (LinearMap.range A.mulVecLin) = n := by
      simpa [Matrix.rank] using hrank
    have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hrange] at hsum
    have hsum' : n + Module.finrank K (LinearMap.ker A.mulVecLin) = n := by
      simpa using hsum
    omega
  · intro hdet
    simpa [Fintype.card_fin] using (Matrix.rank_of_det_ne_zero hdet)

end MathlibPlus.LinearAlgebra
