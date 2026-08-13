import Mathlib

/-!
Elementary exact formalizations of admitted claims 2524 and 12407.

The phase identity retains the literal complex phases from claim 2524.  The
rank statement for claim 12407 is expressed by the displayed two-term
separable decomposition, which is the finite-rank assertion without adding an
unmentioned operator-theoretic framework.
-/

namespace MathlibPlus.Analysis.Claim2524

/-- The phase-normalized cosine identity from admitted claim 2524. -/
theorem phaseNormalization (c t η x : ℝ) :
    let L : ℝ := Real.log c
    let ell : ℝ := L / 2
    let z : ℂ := (t : ℂ) + Complex.I * (η : ℂ)
    2 * Complex.exp (-(η : ℂ) * (ell : ℂ)) *
          Complex.exp (Complex.I * (t : ℂ) * (ell : ℂ)) *
          Complex.cos (z * ((x : ℂ) - (ell : ℂ))) =
      Complex.exp (-(η : ℂ) * (x : ℂ)) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) +
        Complex.exp (-(2 * η : ℝ) * (ell : ℂ)) *
          Complex.exp ((η : ℂ) * (x : ℂ)) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ) +
            2 * Complex.I * (t : ℂ) * (ell : ℂ)) := by
  dsimp
  let a : ℂ := -(η : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)
  let b : ℂ := Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)
  let z : ℂ := (t : ℂ) + Complex.I * (η : ℂ)
  let u : ℂ := (x : ℂ) - ((Real.log c / 2 : ℝ) : ℂ)
  have hmul (p q r : ℂ) :
      Complex.exp p * Complex.exp q * Complex.exp r =
        Complex.exp (p + q + r) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
  have hleft : a + b + Complex.I * z * u =
      -(η : ℂ) * (x : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) := by
    dsimp [a, b, z, u]
    simp only [mul_add, add_mul]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hright : a + b - Complex.I * z * u =
      -(2 * η : ℝ) * ((Real.log c / 2 : ℝ) : ℂ) +
        (η : ℂ) * (x : ℂ) - Complex.I * (t : ℂ) * (x : ℂ) +
          2 * Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ) := by
    dsimp [a, b, z, u]
    simp only [mul_add, add_mul]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  change 2 * Complex.exp a * Complex.exp b * Complex.cos (z * u) = _
  rw [Complex.cos]
  calc
    2 * Complex.exp a * Complex.exp b *
          ((Complex.exp (z * u * Complex.I) +
            Complex.exp (-(z * u) * Complex.I)) / 2) =
        Complex.exp a * Complex.exp b * Complex.exp (z * u * Complex.I) +
          Complex.exp a * Complex.exp b * Complex.exp (-(z * u) * Complex.I) := by
            ring
    _ = Complex.exp (a + b + Complex.I * z * u) +
          Complex.exp (a + b - Complex.I * z * u) := by
            rw [show z * u * Complex.I = Complex.I * z * u by ring,
              show -(z * u) * Complex.I = -Complex.I * z * u by ring]
            rw [hmul, hmul]
            congr 1 <;> ring_nf
    _ = Complex.exp (-(η : ℂ) * (x : ℂ) +
          Complex.I * (t : ℂ) * (x : ℂ)) +
          Complex.exp (-(2 * η : ℝ) * ((Real.log c / 2 : ℝ) : ℂ) +
            (η : ℂ) * (x : ℂ) - Complex.I * (t : ℂ) * (x : ℂ) +
              2 * Complex.I * (t : ℂ) * ((Real.log c / 2 : ℝ) : ℂ)) := by
            rw [hleft, hright]
    _ = _ := by
      simp only [sub_eq_add_neg, Complex.exp_add]
      ring_nf

/-- The phase factor in claim 2524 has unit modulus, giving the associated
real two-component block rotation. -/
theorem phaseFactorUnit (t ell : ℝ) :
    ‖Complex.exp (Complex.I * ((t * ell : ℝ) : ℂ))‖ = 1 := by
  simpa using Complex.norm_exp_I_mul_ofReal (t * ell)

/-- The scalar normalization in claim 2524 is the positive real factor shown
by the exponential form when `c` is positive. -/
theorem scalarNormalization (c η : ℝ) (hc : 0 < c) :
    2 * Real.rpow c (-η / 2) =
      2 * Real.exp (-η * (Real.log c / 2)) := by
  change 2 * c ^ (-η / 2) = 2 * Real.exp (-η * (Real.log c / 2))
  rw [Real.rpow_def_of_pos hc]
  congr 1
  ring

end MathlibPlus.Analysis.Claim2524

namespace MathlibPlus.Analysis.Claim12407

/-- The reflected pole kernel is a sum of two separable kernels. -/
theorem reflectedPoleKernelRankTwo :
    ∃ f₁ f₂ g₁ g₂ : ℝ → ℝ, ∀ x y : ℝ,
      4 * Real.cosh ((x + y) / 2) =
        f₁ x * g₁ y + f₂ x * g₂ y := by
  refine ⟨fun x => 4 * Real.cosh (x / 2), fun x => 4 * Real.sinh (x / 2),
    fun y => Real.cosh (y / 2), fun y => Real.sinh (y / 2), ?_⟩
  intro x y
  rw [show (x + y) / 2 = x / 2 + y / 2 by ring, Real.cosh_add]
  ring

end MathlibPlus.Analysis.Claim12407
