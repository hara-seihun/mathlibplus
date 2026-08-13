import MathlibPlus.Analysis.SymmetricImaginaryShift.ConjugatePair

namespace MathlibPlus.Algebra.ConjugatePair

/-- The modulus-difference identity with the real and imaginary coordinates
ordered as `(x, u, v, y, a)`. -/
theorem modulusDifference (x u v y a : ℝ) :
    let D : ℝ → ℝ := fun Y =>
      ((x - u) ^ 2 + (Y - v) ^ 2) * ((x - u) ^ 2 + (Y + v) ^ 2)
    D (y + a) - D (y - a) =
      8 * a * y * ((x - u) ^ 2 + y ^ 2 + a ^ 2 - v ^ 2) := by
  simpa only using
    (MathlibPlus.Analysis.SymmetricImaginaryShift.conjugatePair_modulusDifference
      u v x y a)

end MathlibPlus.Algebra.ConjugatePair
