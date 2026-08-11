import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim3371

/-- Claim 3371: for an odd number of objects, slack one is equivalent to the
frequency equation and to the half-minus-one frequency. -/
theorem tightFrequencyEquivalence (m f : ℕ) (hm : Odd m) :
    (m - 2 * f = 1) ↔
      (2 * f = m - 1) ∧ (f = (m - 1) / 2) := by
  rcases hm with ⟨k, rfl⟩
  omega

end MathlibPlus.Combinatorics.Claim3371
