import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim16050

/-- Algebraic core of the rooted moment-pencil recursion.  Here `x` is the
product of the child ratios, so the child-product term is `rho * x`. -/
theorem tau_formula
    {R : Type _} [Field R]
    (a q rho x p nu : R)
    (hrho : rho ≠ 0) (hp : p ≠ 0)
    (hpdef : p = a * rho + (q - a) * (rho * x))
    (hnudef : nu = (a - 1) * rho + (q - a) * (rho * x)) :
    nu / p = (a - 1 + (q - a) * x) / (a + (q - a) * x) := by
  let den : R := a + (q - a) * x
  let num : R := a - 1 + (q - a) * x
  have hp_factor : p = rho * den := by
    rw [hpdef]
    dsimp [den]
    ring
  have hnu_factor : nu = rho * num := by
    rw [hnudef]
    dsimp [num]
    ring
  have hden : den ≠ 0 := by
    intro hden
    apply hp
    rw [hp_factor, hden, mul_zero]
  rw [hnu_factor, hp_factor]
  dsimp [den, num] at hden ⊢
  field_simp [hrho, hden]

end MathlibPlus.Algebra.Claim16050
