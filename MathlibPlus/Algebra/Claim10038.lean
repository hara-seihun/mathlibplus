import Mathlib

namespace MathlibPlus.Algebra.Claim10038

/-- Algebraic factorization of the prescribed off-critical branch.  The
analytic zero-free, pole, and Dirichlet-coefficient consequences remain
outside this finite polynomial core. -/
theorem prescribedOffCriticalFactorization_claim10038
    {K : Type*} [Field K] (M : ℕ) (rho X : K) (hrho : rho ≠ 0) :
    (1 + rho * X ^ M) * (1 + rho⁻¹ * X ^ M) =
      1 + (rho + rho⁻¹) * X ^ M + X ^ (2 * M) := by
  field_simp [hrho]
  ring

end MathlibPlus.Algebra.Claim10038
