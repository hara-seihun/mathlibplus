import MathlibPlus.Analysis.SymmetricImaginaryShift.ConjugatePair

/-!
# Elementary identities for symmetric imaginary shifts

This module formalizes the exact algebraic identities in Records 4, 5, and 7 of
source record `C-0024`.  It deliberately does not state the packet's analytic
strip-contraction theorem, which requires a faithful library-level formulation of
its entire-function and order hypotheses.
-/

namespace MathlibPlus.CoshTransfer

/-- The symmetric imaginary-shift transfer `Tₐ F(z) = F(z + ia) + F(z - ia)` from
packet `C-0024`. -/
noncomputable def symmetricImaginaryShift
    (F : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  F (z + a * Complex.I) + F (z - a * Complex.I)

/-- The product of squared distances from `x + iY` to the conjugate pair
`u ± iv`. -/
def conjugatePairDistanceProduct (x u v Y : ℝ) : ℝ :=
  ((x - u) ^ 2 + (Y - v) ^ 2) * ((x - u) ^ 2 + (Y + v) ^ 2)

/-- Exact conjugate-pair modulus-difference identity from Record 4 of packet
`C-0024`. -/
theorem conjugatePairModulusDifference (x y u v a : ℝ) :
    conjugatePairDistanceProduct x u v (y + a) -
        conjugatePairDistanceProduct x u v (y - a) =
      8 * a * y * ((x - u) ^ 2 + y ^ 2 + a ^ 2 - v ^ 2) := by
  simpa [conjugatePairDistanceProduct] using
    (MathlibPlus.Analysis.SymmetricImaginaryShift.conjugatePair_modulusDifference
      u v x y a)

/-- Exact squared-modulus difference for a real zero, Record 5 of packet
`C-0024`. -/
theorem realZeroModulusDifference (x y r a : ℝ) :
    Complex.normSq (((x - r : ℝ) : ℂ) + (y + a) * Complex.I) -
        Complex.normSq (((x - r : ℝ) : ℂ) + (y - a) * Complex.I) =
      4 * a * y := by
  simp [Complex.normSq_apply]
  ring

/-- The quadratic witness attaining the strip-contraction bound in Record 7 of
packet `C-0024`. -/
noncomputable def quadraticStripWitness (u Δ : ℝ) (z : ℂ) : ℂ :=
  (z - u) ^ 2 + Δ ^ 2

/-- The symmetric imaginary shift of the quadratic witness is exactly the quadratic
with squared strip width reduced by `a²`.

The proposal's displayed draft accidentally bound `z : ℝ`; the mathematical prose
states this entire-function identity, so the faithful binder here is `z : ℂ`. -/
theorem quadraticStripWitnessTransfer (u Δ a : ℝ) (z : ℂ) :
    symmetricImaginaryShift (quadraticStripWitness u Δ) a z =
      2 * ((z - u) ^ 2 + Δ ^ 2 - a ^ 2) := by
  simp only [symmetricImaginaryShift, quadraticStripWitness]
  ring_nf
  rw [Complex.I_sq]
  ring

end MathlibPlus.CoshTransfer
