import Mathlib

namespace MathlibPlus.Algebra

open MvPolynomial
noncomputable section

/-- The Poisson--Charlier family from claim 4457, with the displayed
polynomial variable represented by `X 0`. -/
def poissonCharlier_claim4457 (n r : ℕ) : MvPolynomial (Fin 1) ℚ :=
  Nat.rec ((n.factorial : ℚ)⁻¹ • X 0 ^ n)
    (fun _ p => MvPolynomial.pderiv 0 p - p) r

/-- Zeroth Poisson--Charlier polynomial. -/
theorem poissonCharlier_zero_claim4457 (n : ℕ) :
    poissonCharlier_claim4457 n 0 = (n.factorial : ℚ)⁻¹ • X 0 ^ n := by
  rfl

/-- Successor recurrence for the Poisson--Charlier polynomials. -/
theorem poissonCharlier_succ_claim4457 (n r : ℕ) :
    poissonCharlier_claim4457 n (r + 1) =
      MvPolynomial.pderiv 0 (poissonCharlier_claim4457 n r) -
        poissonCharlier_claim4457 n r := by
  rfl

end
end MathlibPlus.Algebra
