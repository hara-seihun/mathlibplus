import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim42851

/-- Claim 42851: the Bézout relation and the scale bound imply the stated
    norm estimate. -/
theorem arbitraryNonnegativeScaleBezoutBound_claim42851
    (A B H J : ℂ) (s C : ℝ) (hs : 0 ≤ s)
    (hbez : A * H + B * J = 1)
    (hbound : s * (‖H‖ + ‖J‖) ≤ C) :
    s ≤ C * max ‖A‖ ‖B‖ := by
  let M : ℝ := max ‖A‖ ‖B‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact le_trans (norm_nonneg A) (le_max_left _ _)
  have hnorm : (1 : ℝ) ≤ M * (‖H‖ + ‖J‖) := by
    have htriangle : (1 : ℝ) ≤ ‖A‖ * ‖H‖ + ‖B‖ * ‖J‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖A * H + B * J‖ := by rw [hbez]
        _ ≤ ‖A * H‖ + ‖B * J‖ := norm_add_le _ _
        _ = ‖A‖ * ‖H‖ + ‖B‖ * ‖J‖ := by rw [norm_mul, norm_mul]
    have hA : ‖A‖ ≤ M := by exact le_max_left _ _
    have hB : ‖B‖ ≤ M := by exact le_max_right _ _
    calc
      (1 : ℝ) ≤ ‖A‖ * ‖H‖ + ‖B‖ * ‖J‖ := htriangle
      _ ≤ M * ‖H‖ + M * ‖J‖ := by
        gcongr
      _ = M * (‖H‖ + ‖J‖) := by ring
  have hs_mul : s ≤ s * (M * (‖H‖ + ‖J‖)) := by
    have := mul_le_mul_of_nonneg_left hnorm hs
    simpa using this
  have hbound_mul := mul_le_mul_of_nonneg_right hbound hM
  calc
    s ≤ s * (M * (‖H‖ + ‖J‖)) := hs_mul
    _ = (s * (‖H‖ + ‖J‖)) * M := by ring
    _ ≤ C * M := hbound_mul
    _ = C * max ‖A‖ ‖B‖ := by rfl

end MathlibPlus.Algebra.Claim42851
