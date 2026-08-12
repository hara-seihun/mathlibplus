import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/-- A primitive integral coordinate direction detects divisibility of its scalar:
the Bezout combination of the coordinates turns coefficientwise divisibility of
`d • D` into divisibility of `d` itself. -/
theorem scalar_dvd_of_coeffwise_dvd_of_primitive
    {ι : Type} [Fintype ι] (q d : ℤ) (D u : ι → ℤ)
    (hbez : ∑ k, u k * D k = 1)
    (hdiv : ∀ k, q ∣ d * D k) :
    q ∣ d := by
  have hsum : q ∣ ∑ k, d * (u k * D k) := by
    apply Finset.dvd_sum
    intro k hk
    rcases hdiv k with ⟨t, ht⟩
    refine ⟨u k * t, ?_⟩
    calc
      d * (u k * D k) = u k * (d * D k) := by ring
      _ = u k * (q * t) := by rw [ht]
      _ = q * (u k * t) := by ring
  convert hsum using 1
  rw [← Finset.mul_sum]
  simp [hbez]

/-- Coefficientwise congruence of two points on a primitive integral axis is
exactly congruence of their scalar coordinates. -/
theorem coeffwise_congruent_iff_scalar_congruent_of_primitive
    {ι : Type} [Fintype ι] (q cᵢ cⱼ : ℤ) (D u : ι → ℤ)
    (hbez : ∑ k, u k * D k = 1) :
    (∀ k, q ∣ (cᵢ - cⱼ) * D k) ↔ q ∣ cᵢ - cⱼ := by
  constructor
  · exact scalar_dvd_of_coeffwise_dvd_of_primitive q (cᵢ - cⱼ) D u hbez
  · intro h k
    exact dvd_mul_of_dvd_left h (D k)

end MathlibPlus.LinearAlgebra
