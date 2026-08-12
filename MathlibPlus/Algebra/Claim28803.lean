import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 28803: the four displayed forest products have the stated ratios.
The source's connected factors are represented pointwise in an arbitrary
field; `hA` and `hB` are exactly the nonvanishing denominator conditions. -/
theorem fourForestProducts_ratios_claim28803
    {K : Type*} [Field K]
    (f D a b : K)
    (_ha : a ≠ 0) (_hb : b ≠ 0) (_hab : a ≠ b) (_habNeg : a ≠ -b)
    (hA : f - a * D ≠ 0) (hB : f - b * D ≠ 0) :
    let F₀ := (f - a * D) ^ 2 * (f - b * D)
    let F₂a := (f - a * D) * (f + a * D) * (f - b * D)
    let F₄a := (f + a * D) ^ 2 * (f - b * D)
    let F₂ab := (f - a * D) * (f + a * D) * (f + b * D)
    F₀ / F₀ = 1 ∧
      F₂a / F₀ = (f + a * D) / (f - a * D) ∧
      F₄a / F₀ = ((f + a * D) / (f - a * D)) ^ 2 ∧
      F₂ab / F₀ = ((f + a * D) / (f - a * D)) *
        ((f + b * D) / (f - b * D)) := by
  dsimp
  have hB' : f - D * b ≠ 0 := by simpa [mul_comm] using hB
  have hF₀ : (f - a * D) ^ 2 * (f - b * D) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hA) hB
  constructor
  · exact div_self hF₀
  constructor
  · field_simp [hA, hB, hB']
  constructor
  · field_simp [hA, hB, hB']
  · field_simp [hA, hB, hB']

end MathlibPlus.Algebra
