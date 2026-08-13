import Mathlib

namespace MathlibPlus.Analysis.BasicFormResonance

/--
Claim 21431.  The heat-equation zero-velocity consequence is stated at the
exact scalar derivative interface: `Ht` is the time derivative, `Hx` the
nonzero spatial derivative on the simple branch, and `Hxx` the second spatial
derivative.  The chain-rule relation for the zero branch is retained as an
explicit hypothesis rather than silently assuming regularity of `H`.
-/
theorem zeroVelocity_from_heat_equation_claim21431
    (Ht Hx Hxx xdot : ℝ)
    (hheat : Ht = -Hxx)
    (hzero : Ht + Hx * xdot = 0)
    (hsimple : Hx ≠ 0) :
    xdot = Hxx / Hx := by
  rw [eq_div_iff hsimple]
  nlinarith

end MathlibPlus.Analysis.BasicFormResonance
