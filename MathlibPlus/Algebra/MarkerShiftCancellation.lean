import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra

noncomputable section

/--
The explicit cancellation in claim 58419 (R-4542 S5).  The source's
``Phi_t`` is represented on the free commutative polynomial algebra by the
Z-linear map sending a monomial `z^r * x^lambda` to
`x_(r+t) * x^lambda`; the six terms of `D_t` are written as exponent
vectors, so no normal-form or source-specific oracle is used.
-/
theorem markerShiftExplicitCancellation (t : ℕ) :
    let markerExponent : ℕ → (Option ℕ →₀ ℕ) → (ℕ →₀ ℕ) := fun _t p =>
      Finsupp.single (p none + _t) 1 +
        p.comapDomain some (Option.some_injective _).injOn
    let markerMap : ∀ t, MvPolynomial (Option ℕ) ℤ →ₗ[ℤ] MvPolynomial ℕ ℤ :=
      fun t =>
        (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
          ((Finsupp.linearCombination ℤ (fun p : Option ℕ →₀ ℕ =>
            AddMonoidAlgebra.coeff
              (MvPolynomial.monomial (markerExponent t p) (1 : ℤ)))).comp
            (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)
    let markerD : ∀ t, MvPolynomial (Option ℕ) ℤ := fun t =>
      MvPolynomial.monomial
          (Finsupp.single none 1 + Finsupp.single (some t) 1 +
            Finsupp.single (some (t + 3)) 1) 1
        - MvPolynomial.monomial
          (Finsupp.single none 2 + Finsupp.single (some t) 1 +
            Finsupp.single (some (t + 2)) 1) 1
        - MvPolynomial.monomial
          (Finsupp.single (some (t + 1)) 1 +
            Finsupp.single (some (t + 3)) 1) 1
        + MvPolynomial.monomial
          (Finsupp.single none 2 + Finsupp.single (some (t + 1)) 2) 1
        + MvPolynomial.monomial (Finsupp.single (some (t + 2)) 2) 1
        - MvPolynomial.monomial
          (Finsupp.single none 1 + Finsupp.single (some (t + 1)) 1 +
            Finsupp.single (some (t + 2)) 1) 1
    markerMap t (markerD t) = 0 := by
  let markerExponent : ℕ → (Option ℕ →₀ ℕ) → (ℕ →₀ ℕ) := fun t p =>
    Finsupp.single (p none + t) 1 +
      p.comapDomain some (Option.some_injective _).injOn
  let markerMap : ∀ t, MvPolynomial (Option ℕ) ℤ →ₗ[ℤ] MvPolynomial ℕ ℤ :=
    fun t =>
      (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
        ((Finsupp.linearCombination ℤ (fun p : Option ℕ →₀ ℕ =>
          AddMonoidAlgebra.coeff
            (MvPolynomial.monomial (markerExponent t p) (1 : ℤ)))).comp
          (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)
  let markerD : ∀ t, MvPolynomial (Option ℕ) ℤ := fun t =>
    MvPolynomial.monomial
        (Finsupp.single none 1 + Finsupp.single (some t) 1 +
          Finsupp.single (some (t + 3)) 1) 1
      - MvPolynomial.monomial
        (Finsupp.single none 2 + Finsupp.single (some t) 1 +
          Finsupp.single (some (t + 2)) 1) 1
      - MvPolynomial.monomial
        (Finsupp.single (some (t + 1)) 1 +
          Finsupp.single (some (t + 3)) 1) 1
      + MvPolynomial.monomial
        (Finsupp.single none 2 + Finsupp.single (some (t + 1)) 2) 1
      + MvPolynomial.monomial (Finsupp.single (some (t + 2)) 2) 1
      - MvPolynomial.monomial
        (Finsupp.single none 1 + Finsupp.single (some (t + 1)) 1 +
          Finsupp.single (some (t + 2)) 1) 1
  change markerMap t (markerD t) = 0
  have markerMap_monomial (t : ℕ) (p : Option ℕ →₀ ℕ) (c : ℤ) :
      markerMap t (MvPolynomial.monomial p c) =
        MvPolynomial.monomial (markerExponent t p) c := by
    change AddMonoidAlgebra.ofCoeff
        ((Finsupp.linearCombination ℤ (fun p : Option ℕ →₀ ℕ =>
          AddMonoidAlgebra.coeff
            (MvPolynomial.monomial (markerExponent t p) (1 : ℤ))))
          (Finsupp.single p c)) = _
    rw [Finsupp.linearCombination_single]
    simp [MvPolynomial.monomial]
  have h13 :
      markerExponent t
          (Finsupp.single none 1 + Finsupp.single (some t) 1 +
            Finsupp.single (some (t + 3)) 1) =
        markerExponent t
          (Finsupp.single (some (t + 1)) 1 +
            Finsupp.single (some (t + 3)) 1) := by
    classical
    ext i
    cases i <;> simp [markerExponent, Finsupp.single_apply] <;> split_ifs <;> omega
  have h25 :
      markerExponent t
          (Finsupp.single none 2 + Finsupp.single (some t) 1 +
            Finsupp.single (some (t + 2)) 1) =
        markerExponent t (Finsupp.single (some (t + 2)) 2) := by
    classical
    ext i
    cases i <;> simp [markerExponent, Finsupp.single_apply] <;> split_ifs <;> omega
  have h46 :
      markerExponent t
          (Finsupp.single none 2 + Finsupp.single (some (t + 1)) 2) =
        markerExponent t
          (Finsupp.single none 1 + Finsupp.single (some (t + 1)) 1 +
            Finsupp.single (some (t + 2)) 1) := by
    classical
    ext i
    cases i <;> simp [markerExponent, Finsupp.single_apply] <;> split_ifs <;> omega
  simp only [markerD, map_sub, map_add, markerMap_monomial]
  rw [h13, h25, h46]
  abel

end
end MathlibPlus.Algebra
