import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim15208

noncomputable section

/-- The base polynomial in the affine trace-correction calculation. -/
def ell : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.X - Polynomial.C 3

/-- The quotient polynomial after an integral correction `c`. -/
def q (c : Polynomial ℤ) : Polynomial ℤ := ell - Polynomial.C 2 * c

/-- The associated remainder polynomial. -/
def r (c : Polynomial ℤ) : Polynomial ℤ :=
  (Polynomial.X + Polynomial.C 1) * q c + Polynomial.X * c

def c₁ : Polynomial ℤ := Polynomial.X
def c₂ : Polynomial ℤ := Polynomial.X + Polynomial.C 1

theorem q_c₁ : q c₁ = Polynomial.X ^ 2 - Polynomial.C 3 * Polynomial.X - Polynomial.C 3 := by
  dsimp [q, c₁, ell]
  simp
  ring

theorem r_c₁ : r c₁ = Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.C 6 * Polynomial.X - Polynomial.C 3 := by
  dsimp [r, q, c₁, ell]
  simp
  ring

theorem q_c₂ : q c₂ = Polynomial.X ^ 2 - Polynomial.C 3 * Polynomial.X - Polynomial.C 5 := by
  dsimp [q, c₂, ell]
  simp
  ring

theorem r_c₂ : r c₂ = Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.C 7 * Polynomial.X - Polynomial.C 5 := by
  dsimp [r, q, c₂, ell]
  simp
  ring

end
end MathlibPlus.Algebra.Claim15208
