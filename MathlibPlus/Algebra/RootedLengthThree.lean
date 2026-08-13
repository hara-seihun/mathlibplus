import MathlibPlus.Basic

namespace MathlibPlus.Algebra.RootedLengthThree

/-- The local length-three residual identity from Claim 27584.  The ambient
rooted-tree carrier and positive orbit gauges are intentionally not hidden in
this algebraic core. -/
theorem residual_derivative
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (a b c : R)
    (h : D a = b ∧ D b = 2 * a * a ∧ D c = a * b + b * a) :
    D (c - a * a) = 0 := by
  rcases h with ⟨ha, _, hc⟩
  rw [show D (c - a * a) = D c - D (a * a) by
    exact D.toLinearMap.map_sub _ _]
  rw [hc, D.leibniz, ha]
  simp only [smul_eq_mul]
  ring

end MathlibPlus.Algebra.RootedLengthThree
