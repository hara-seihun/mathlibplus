import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/-- Row/column signs cannot alter a strictly positive matrix while keeping all
entries nonnegative.  The claim's displayed even-order minor is an instance of
this general square-matrix statement. -/
theorem positiveMatrixSignGaugePreservesMinor19425 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n → ℝ)
    (hA : ∀ i j, 0 < A i j)
    (hr : ∀ i, r i = 1 ∨ r i = -1)
    (hc : ∀ j, c j = 1 ∨ c j = -1)
    (hnonneg : ∀ i j, 0 ≤ r i * A i j * c j) :
    (fun i j => r i * A i j * c j) = A ∧
      Matrix.det (fun i j => r i * A i j * c j) = Matrix.det A ∧
      (Matrix.det A < 0 → Matrix.det (fun i j => r i * A i j * c j) < 0) := by
  have hentry : ∀ i j, r i * A i j * c j = A i j := by
    intro i j
    rcases hr i with hri | hri
    · rcases hc j with hcj | hcj
      · simp [hri, hcj]
      · have h := hnonneg i j
        rw [hri, hcj] at h
        nlinarith [hA i j]
    · rcases hc j with hcj | hcj
      · have h := hnonneg i j
        rw [hri, hcj] at h
        nlinarith [hA i j]
      · simp [hri, hcj]
  have hmat : (fun i j => r i * A i j * c j) = A := by
    funext i j
    exact hentry i j
  refine ⟨hmat, ?_, ?_⟩
  · rw [hmat]
  · intro hdet
    rw [hmat]
    exact hdet

end MathlibPlus.LinearAlgebra
