import Mathlib.Tactic

namespace MathlibPlus.AlgebraicGeometry.Claim55590

/--
Claim 55590 is numerical bookkeeping only.  The hypotheses say exactly that
`p_g = a - 1` and `h^(1,1) = a + d` are nonnegative formal values; no surface or
Hodge-structure existence assertion is introduced.
-/
theorem formalHodgeBookkeeping (a d : ℤ)
    (hpg : 0 ≤ a - 1) (hh : 0 ≤ a + d) :
    0 ≤ (0 : ℤ) ∧
      0 ≤ a - 1 ∧
      0 ≤ a + d ∧
      1 - 0 + (a - 1) = a ∧
      2 + 2 * (a - 1) + (a + d) = 3 * a + d ∧
      (1 + 2 * (a - 1)) - ((a + d) - 1) = a - d := by
  refine ⟨by omega, hpg, hh, ?_, ?_, ?_⟩ <;> ring

end MathlibPlus.AlgebraicGeometry.Claim55590
