import Mathlib

namespace MathlibPlus.Algebra

/-- The reflected Euler atom admits the Laurent factorization from claim 50802.
The two convergence hypotheses are retained in the statement, although the
identity itself is algebraic. -/
theorem claim50802_reflected_euler_factorization
    (p : ℕ) (_hp : Nat.Prime p) (s : ℂ) (r : ℝ) (hr : 0 < r)
    (_h₁ : ‖(r : ℂ) * Complex.exp (-(Real.log (p : ℝ) : ℂ) *
      (s - (1 / 2 : ℂ)))‖ < 1)
    (_h₂ : ‖(r : ℂ)⁻¹ * Complex.exp (-(Real.log (p : ℝ) : ℂ) *
      (s - (1 / 2 : ℂ)))‖ < 1) :
    let lambda : ℝ := Real.log (p : ℝ)
    let z : ℂ := s - (1 / 2 : ℂ)
    let x : ℂ := Complex.exp (-(lambda : ℂ) * z)
    let B : ℂ :=
      (1 + (r : ℂ) * Complex.exp ((lambda : ℂ) * z)) *
        (1 + (r : ℂ) * Complex.exp (-(lambda : ℂ) * z))
    B = (r : ℂ) * x⁻¹ * (1 + (r : ℂ) * x) *
      (1 + (r : ℂ)⁻¹ * x) := by
  dsimp
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  let a : ℂ := (Real.log (p : ℝ) : ℂ) * (s - (1 / 2 : ℂ))
  have hx_inv : (Complex.exp (-a))⁻¹ = Complex.exp a := by
    simp [Complex.exp_neg]
  have hprod : Complex.exp a * Complex.exp (-a) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hprod_r2 : (r : ℂ) ^ 2 * Complex.exp a * Complex.exp (-a) =
      (r : ℂ) ^ 2 := by
    calc
      (r : ℂ) ^ 2 * Complex.exp a * Complex.exp (-a) =
          (r : ℂ) ^ 2 * (Complex.exp a * Complex.exp (-a)) := by ring
      _ = (r : ℂ) ^ 2 * 1 := by rw [hprod]
      _ = (r : ℂ) ^ 2 := by ring
  have hprod_r : (r : ℂ) * Complex.exp a * Complex.exp (-a) ^ 2 =
      (r : ℂ) * Complex.exp (-a) := by
    calc
      (r : ℂ) * Complex.exp a * Complex.exp (-a) ^ 2 =
          (r : ℂ) * (Complex.exp a * Complex.exp (-a) ^ 2) := by ring
      _ = (r : ℂ) * ((Complex.exp a * Complex.exp (-a)) *
          Complex.exp (-a)) := by ring
      _ = (r : ℂ) * (1 * Complex.exp (-a)) := by rw [hprod]
      _ = (r : ℂ) * Complex.exp (-a) := by ring
  have hneg : -(Real.log (p : ℝ) : ℂ) * (s - (1 / 2 : ℂ)) =
      -((Real.log (p : ℝ) : ℂ) * (s - (1 / 2 : ℂ))) := by ring
  rw [hneg]
  change (1 + (r : ℂ) * Complex.exp a) * (1 + (r : ℂ) * Complex.exp (-a)) =
    (r : ℂ) * (Complex.exp (-a))⁻¹ * (1 + (r : ℂ) * Complex.exp (-a)) *
      (1 + (r : ℂ)⁻¹ * Complex.exp (-a))
  rw [hx_inv]
  field_simp [hr0]
  ring_nf
  rw [hprod_r2, hprod_r, hprod]
  ring

end MathlibPlus.Algebra
