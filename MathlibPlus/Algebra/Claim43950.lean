import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim43950

local notation "A" => MvPolynomial (Fin 2) (ZMod 2)
local notation "u" => (Polynomial.C (MvPolynomial.X (0 : Fin 2)) : Polynomial A)
local notation "s" => (Polynomial.C (MvPolynomial.X (1 : Fin 2)) : Polynomial A)
local notation "t" => (Polynomial.X : Polynomial A)

/-- The exact rooted-factor calculation for the order-four pair in R-2305. -/
theorem rooted_factor_difference_claim43950 :
    let a : Polynomial A := t + u
    let b : Polynomial A := u * s + t * a
    let fS : Polynomial A := u * s ^ 2 + t * a ^ 2
    let fP : Polynomial A := u * s ^ 2 + t * b
    fS + fP = u * t * (u + s + t) ∧
      (fS + fP).natDegree = 2 := by
  dsimp
  constructor
  · ring_nf
    have h2 : (2 : A) = 0 := by
      change MvPolynomial.C (2 : ZMod 2) = 0
      have hz : (2 : ZMod 2) = 0 := by decide
      rw [hz]
      simp
    have h3 : (3 : A) = 1 := by
      change MvPolynomial.C (3 : ZMod 2) = 1
      have hz : (3 : ZMod 2) = 1 := by decide
      rw [hz]
      simp
    have hp2 : (2 : Polynomial A) = 0 := by
      change Polynomial.C (2 : A) = 0
      rw [h2]
      simp
    have hp3 : (3 : Polynomial A) = 1 := by
      change Polynomial.C (3 : A) = 1
      rw [h3]
      simp
    simp [hp2, hp3]
  · rw [show u * s ^ 2 + t * (t + u) ^ 2 +
      (u * s ^ 2 + t * (u * s + t * (t + u))) =
      u * t * (u + s + t) by
        ring_nf
        have h2 : (2 : A) = 0 := by
          change MvPolynomial.C (2 : ZMod 2) = 0
          have hz : (2 : ZMod 2) = 0 := by decide
          rw [hz]
          simp
        have h3 : (3 : A) = 1 := by
          change MvPolynomial.C (3 : ZMod 2) = 1
          have hz : (3 : ZMod 2) = 1 := by decide
          rw [hz]
          simp
        have hp2 : (2 : Polynomial A) = 0 := by
          change Polynomial.C (2 : A) = 0
          rw [h2]
          simp
        have hp3 : (3 : Polynomial A) = 1 := by
          change Polynomial.C (3 : A) = 1
          rw [h3]
          simp
        simp [hp2, hp3]]
    have hu : (MvPolynomial.X (0 : Fin 2) : A) ≠ 0 := by simp
    have hlin : (u + s + t : Polynomial A) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun p : Polynomial A => p.coeff 1) h
      norm_num at hcoeff
    have hsum : (u + s + t : Polynomial A) = t + (u + s) := by ring
    have hlin' : (t + (u + s) : Polynomial A) ≠ 0 := by
      rw [← hsum]
      exact hlin
    rw [hsum]
    have hlinDegree : (t + (u + s) : Polynomial A).natDegree = 1 := by
      rw [← Polynomial.C_add, Polynomial.natDegree_X_add_C]
    rw [Polynomial.natDegree_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr hu)
        Polynomial.X_ne_zero) hlin', hlinDegree]
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hu) Polynomial.X_ne_zero]
    norm_num

end MathlibPlus.Algebra.Claim43950
