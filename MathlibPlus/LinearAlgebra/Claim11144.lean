import Mathlib.Algebra.Ring.Basic

namespace MathlibPlus.LinearAlgebra.Claim11144

/-- In any associative ring, an involutive grading converts the chiral
conjugation identity into anticommutation.  The source-specific current and
cutoff operators are deliberately left as the ring elements `J` and `Γ`. -/
theorem chiralAnticommutation_of_conjugation_claim11144
    {R : Type*} [Ring R] (Γ J : R)
    (hΓ : Γ * Γ = 1) (hconj : Γ * J * Γ = -J) :
    Γ * J = -J * Γ := by
  calc
    Γ * J = (Γ * J) * 1 := by rw [mul_one]
    _ = (Γ * J) * (Γ * Γ) := by rw [hΓ]
    _ = (Γ * J * Γ) * Γ := by simp only [mul_assoc]
    _ = (-J) * Γ := by rw [hconj]

/-- With `Γ²=1`, the conjugation and anticommutation formulations in claim
11144 are equivalent, not merely one-way implications. -/
theorem chiralAnticommutation_iff_claim11144
    {R : Type*} [Ring R] (Γ J : R) (hΓ : Γ * Γ = 1) :
    Γ * J * Γ = -J ↔ Γ * J = -J * Γ := by
  constructor
  · exact chiralAnticommutation_of_conjugation_claim11144 Γ J hΓ
  · intro hanti
    calc
      Γ * J * Γ = (-J * Γ) * Γ := by rw [hanti]
      _ = -J * (Γ * Γ) := by simp only [mul_assoc]
      _ = -J := by rw [hΓ, mul_one]

end MathlibPlus.LinearAlgebra.Claim11144
