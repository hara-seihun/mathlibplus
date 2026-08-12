import Mathlib

namespace MathlibPlus.Combinatorics.Claim31558

/-- Claim 31558: in a cyclic profile of three outer signs, one adjacent pair
has equal signs.  The indices `0`, `1`, and `2` give the ordered pairs
`(ε₁, ε₀)`, `(ε₂, ε₁)`, and `(ε₀, ε₂)`, respectively. -/
theorem adjacentEqualOuterSign
    (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ i : Fin 3, ε (i + 1) = ε i := by
  by_contra h
  push Not at h
  have h01 : ε (1 : Fin 3) ≠ ε 0 := by
    simpa using h (0 : Fin 3)
  have h12 : ε (2 : Fin 3) ≠ ε 1 := by
    simpa using h (1 : Fin 3)
  have h20 : ε (0 : Fin 3) ≠ ε 2 := by
    simpa using h (2 : Fin 3)
  rcases hε 0 with h0 | h0 <;>
    rcases hε 1 with h1 | h1 <;>
    rcases hε 2 with h2 | h2 <;>
    omega

end MathlibPlus.Combinatorics.Claim31558
