import Mathlib

namespace MathlibPlus.Algebra.CayleyPair

/-- Claim 18010 in an arbitrary real algebra: an involution and the identity
operator satisfy the displayed hyperbolic Cayley relations. -/
theorem cayleyPairAlgebra {A : Type*} [Semiring A] [Algebra ℝ A]
    (sigma : A) (hsigma : sigma * sigma = 1) (ξ : ℝ) :
    let X : A := Real.tanh ξ • sigma
    let Y : A := (1 / Real.cosh ξ) • (1 : A)
    X * Y = Y * X ∧ X * X + Y * Y = 1 := by
  dsimp
  have hc : Real.cosh ξ ≠ 0 := ne_of_gt (Real.cosh_pos ξ)
  have hs : Real.tanh ξ ^ 2 + (1 / Real.cosh ξ) ^ 2 = 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq ξ]
  constructor
  · simp [smul_smul, mul_comm]
  · simp [smul_smul, hsigma]
    have h := congrArg (fun r : ℝ => r • (1 : A)) hs
    simpa [pow_two, add_smul] using h

end MathlibPlus.Algebra.CayleyPair
