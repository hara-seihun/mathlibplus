import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim58420

noncomputable section

/-- Exact adjacent-shift cancellation in claim 58420 (R-4542 S6). -/
theorem phiSuccCancellation_claim58420 (t : ℕ) :
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
    markerMap (t + 1) (markerD t) = 0 := by
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
  change markerMap (t + 1) (markerD t) = 0
  have markerMap_monomial (s : ℕ) (p : Option ℕ →₀ ℕ) (c : ℤ) :
      markerMap s (MvPolynomial.monomial p c) =
        MvPolynomial.monomial (markerExponent s p) c := by
    change AddMonoidAlgebra.ofCoeff
        ((Finsupp.linearCombination ℤ (fun p : Option ℕ →₀ ℕ =>
          AddMonoidAlgebra.coeff
            (MvPolynomial.monomial (markerExponent s p) (1 : ℤ))))
          (Finsupp.single p c)) = _
    rw [Finsupp.linearCombination_single]
    simp [MvPolynomial.monomial]
  have h12 :
      markerExponent (t + 1)
          (Finsupp.single none 1 + Finsupp.single (some t) 1 +
            Finsupp.single (some (t + 3)) 1) =
        markerExponent (t + 1)
          (Finsupp.single none 2 + Finsupp.single (some t) 1 +
            Finsupp.single (some (t + 2)) 1) := by
    classical
    ext i
    cases i <;> simp [markerExponent, Finsupp.single_apply] <;> split_ifs <;> omega
  have h34 :
      markerExponent (t + 1)
          (Finsupp.single (some (t + 1)) 1 +
            Finsupp.single (some (t + 3)) 1) =
        markerExponent (t + 1)
          (Finsupp.single none 2 + Finsupp.single (some (t + 1)) 2) := by
    classical
    ext i
    cases i <;> simp [markerExponent, Finsupp.single_apply] <;> split_ifs <;> omega
  have h56 :
      markerExponent (t + 1)
          (Finsupp.single (some (t + 2)) 2) =
        markerExponent (t + 1)
          (Finsupp.single none 1 + Finsupp.single (some (t + 1)) 1 +
            Finsupp.single (some (t + 2)) 1) := by
    classical
    ext i
    cases i <;> simp [markerExponent, Finsupp.single_apply] <;> split_ifs <;> omega
  simp only [markerD, map_sub, map_add, markerMap_monomial]
  rw [h12, h34, h56]
  abel

end
end MathlibPlus.Algebra.Claim58420
