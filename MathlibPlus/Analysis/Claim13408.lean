import Mathlib

namespace MathlibPlus.Analysis.Claim13408

/-- The finite Euler product over primes at most the natural cutoff.  The
complex-power branch is Mathlib's `Complex.cpow` branch. -/
noncomputable def finiteEulerProduct (y : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    (1 - Complex.cpow (p : ℂ) (-z))

theorem finiteEulerProduct_eq (y : ℕ) (z : ℂ) :
    finiteEulerProduct y z =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - Complex.cpow (p : ℂ) (-z)) := by
  rfl

end MathlibPlus.Analysis.Claim13408
