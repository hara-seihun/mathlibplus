import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim38341

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/--
For two monic factors affine in `y`, equality of their formal `x`-derivatives
forces equality of the `x`-derivatives of both the sum and product of their
constant terms.  In characteristic zero, those two differences are constant
polynomials.

The local derivation in the premise is coefficientwise formal differentiation
in `x` on `K[X][Y]`; `Y` is the displayed `y` variable.
-/
theorem sumAndProductConstants
    (m : ℕ) (A B C D : Polynomial K)
    (_hA : A.Monic) (_hB : B.Monic) (_hC : C.Monic) (_hD : D.Monic)
    (_hAm : A.natDegree = m) (_hBm : B.natDegree = m)
    (_hCm : C.natDegree = m) (_hDm : D.natDegree = m)
    (h :
      let Dx : Derivation K (Polynomial (Polynomial K)) (Polynomial (Polynomial K)) :=
        PolynomialModule.equivPolynomialSelf.compDer
          (Polynomial.derivative'.mapCoeffs)
      Dx ((Polynomial.X + Polynomial.C A) * (Polynomial.X + Polynomial.C B)) =
        Dx ((Polynomial.X + Polynomial.C C) * (Polynomial.X + Polynomial.C D))) :
    ∃ a b : K,
      A + B - C - D = Polynomial.C a ∧
      A * B - C * D = Polynomial.C b := by
  let Dx : Derivation K (Polynomial (Polynomial K)) (Polynomial (Polynomial K)) :=
    PolynomialModule.equivPolynomialSelf.compDer
      (Polynomial.derivative'.mapCoeffs)
  change Dx ((Polynomial.X + Polynomial.C A) * (Polynomial.X + Polynomial.C B)) =
      Dx ((Polynomial.X + Polynomial.C C) * (Polynomial.X + Polynomial.C D)) at h
  have coeff_Dx (p : Polynomial (Polynomial K)) (n : ℕ) :
      (Dx p).coeff n = (p.coeff n).derivative := by
    dsimp [Dx]
    rfl
  have h₁ := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 1) h
  have h₀ := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 0) h
  rw [coeff_Dx, coeff_Dx] at h₁ h₀
  have hsum : Polynomial.derivative (A + B) = Polynomial.derivative (C + D) := by
    simpa [Polynomial.mul_coeff_one] using h₁
  have hprod : Polynomial.derivative (A * B) = Polynomial.derivative (C * D) := by
    simpa [Polynomial.mul_coeff_zero] using h₀
  have hsum0 : Polynomial.derivative (A + B - C - D) = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sub, hsum,
      Polynomial.derivative_add]
    abel
  have hprod0 : Polynomial.derivative (A * B - C * D) = 0 := by
    rw [Polynomial.derivative_sub, hprod]
    abel
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp
    (Polynomial.derivative_eq_zero.mp hsum0)
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.mp
    (Polynomial.derivative_eq_zero.mp hprod0)
  exact ⟨a, b, ha.symm, hb.symm⟩

end
end MathlibPlus.Algebra.Claim38341
