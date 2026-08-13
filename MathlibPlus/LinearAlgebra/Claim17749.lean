import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim17749

noncomputable section

/-- The weighted Hankel slope matrix from claim 17749. -/
def vacuumSlopeMatrix (N : ℕ) (d : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ) / 2 *
      d ((i : ℕ) + (j : ℕ) + 1)

@[simp] theorem vacuumSlopeMatrix_apply
    (N : ℕ) (d : ℕ → ℝ) (i j : Fin N) :
    vacuumSlopeMatrix N d i j =
      (((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ) / 2 *
        d ((i : ℕ) + (j : ℕ) + 1) := rfl

/-- Entries of the slope matrix agree whenever the two index sums agree. -/
theorem vacuumSlopeMatrix_depends_only_on_index_sum
    (N : ℕ) (d : ℕ → ℝ) (i j i' j' : Fin N)
    (h : (i : ℕ) + (j : ℕ) = (i' : ℕ) + (j' : ℕ)) :
    vacuumSlopeMatrix N d i j = vacuumSlopeMatrix N d i' j' := by
  simp only [vacuumSlopeMatrix_apply]
  rw [h]

end

end MathlibPlus.LinearAlgebra.Claim17749
