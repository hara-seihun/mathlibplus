import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/--
The exact natural-number obstruction isolated in admitted claim 51736.  The
source's `q₁` and its mode are not defined in the packet; `modeQ₁` and
`h_mode` expose the source assertion `mode(q₁) < m₁` rather than silently
inventing a polynomial or mode convention.
-/
theorem modeApplicationObstruction_claim51736
    (m₁ m₂ m₃ modeQ₁ : ℕ)
    (h_monotone : m₂ ≤ m₃)
    (h_alternating : 2 * (m₁ + m₃) < 3 * m₂)
    (h_mode : modeQ₁ < m₁) :
    2 * m₁ < m₂ ∧
      m₁ < m₂ - m₁ ∧
      modeQ₁ < m₂ - m₁ ∧
      ¬ (m₂ - m₁ ≤ modeQ₁) := by
  omega

end MathlibPlus.Analysis
