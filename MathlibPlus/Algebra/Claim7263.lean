import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- Claim 7263: unequal ordered amplitudes combine with the stated
size-barycentric weights after the common exponential factor is restored. -/
theorem claim7263_barycentricRecombination
    (n m : ℕ) (hnm : 0 < n + m) (A B u d : ℝ) :
    ((n : ℝ) / (n + m)) * A * Real.exp (-u * d * (n + m)) +
        ((m : ℝ) / (n + m)) * B * Real.exp (-u * d * (n + m)) =
      ((n * A + m * B : ℝ) / (n + m)) *
        Real.exp (-u * d * (n + m)) := by
  have hnm' : (n + m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnm)
  field_simp [hnm']

end MathlibPlus.Algebra
