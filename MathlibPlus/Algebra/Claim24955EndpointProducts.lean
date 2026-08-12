import Mathlib

namespace MathlibPlus.Algebra.Claim24955EndpointProducts

/-- Claim 24955: a divisor of the two coefficients of a quadratic product
-difference divides each of the four cross-endpoint products. -/
theorem content_dvd_endpointProducts
    {R : Type*} [CommRing R]
    (h a b c d : R)
    (hα : h ∣ c + d - a - b)
    (hβ : h ∣ c * d - a * b) :
    h ∣ (c - a) * (d - a) ∧
      h ∣ (c - b) * (d - b) ∧
      h ∣ (a - c) * (b - c) ∧
      h ∣ (a - d) * (b - d) := by
  rcases hα with ⟨u, hu⟩
  rcases hβ with ⟨v, hv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨v - a * u, ?_⟩
    calc
      (c - a) * (d - a) = (c * d - a * b) - a * (c + d - a - b) := by ring
      _ = h * v - a * (h * u) := by rw [hv, hu]
      _ = h * (v - a * u) := by ring
  · refine ⟨v - b * u, ?_⟩
    calc
      (c - b) * (d - b) = (c * d - a * b) - b * (c + d - a - b) := by ring
      _ = h * v - b * (h * u) := by rw [hv, hu]
      _ = h * (v - b * u) := by ring
  · refine ⟨c * u - v, ?_⟩
    calc
      (a - c) * (b - c) = c * (c + d - a - b) - (c * d - a * b) := by ring
      _ = c * (h * u) - h * v := by rw [hv, hu]
      _ = h * (c * u - v) := by ring
  · refine ⟨d * u - v, ?_⟩
    calc
      (a - d) * (b - d) = d * (c + d - a - b) - (c * d - a * b) := by ring
      _ = d * (h * u) - h * v := by rw [hv, hu]
      _ = h * (d * u - v) := by ring

end MathlibPlus.Algebra.Claim24955EndpointProducts
