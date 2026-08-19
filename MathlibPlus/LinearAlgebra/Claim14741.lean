import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim14741

/-- Left and right fixed channel matrices cannot increase the rank of a middle
matrix. -/
theorem separateRankBound {m : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (L : Matrix α (Fin m) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (R : Matrix (Fin m) β ℂ) :
    (L * B * R).rank ≤ B.rank ∧ B.rank ≤ m := by
  constructor
  · exact (Matrix.rank_mul_le_left (L * B) R).trans (Matrix.rank_mul_le_right L B)
  · exact Matrix.rank_le_width B

end MathlibPlus.LinearAlgebra.Claim14741
