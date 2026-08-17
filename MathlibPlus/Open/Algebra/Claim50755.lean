import MathlibPlus.Algebra.Claim50754

open scoped LaurentPolynomial BigOperators

namespace MathlibPlus.Open.Algebra.Claim50755

/-- The imposed one-generator Laurent quotient has the displayed degree-four
rewrite, its commuting critical-pair filler, and the stated Laurent normal
forms. -/
def terminatingLaurentRewrite : Prop :=
  let A := ℚ[T;T⁻¹]
  let q : A := LaurentPolynomial.T 1
  let qInv : A := LaurentPolynomial.T (-1)
  let pIn : A := (5 * q + 4) * (4 * q + 5)
  let pOut : A := (2 * q + 1) * (q + 2)
  let p : A := pIn * pOut
  let I := Ideal.span ({p} : Set A)
  let Q := A ⧸ I
  let qbar : Q := Ideal.Quotient.mk I q
  let qInvBar : Q := Ideal.Quotient.mk I qInv
  let cast : ℚ → Q := algebraMap ℚ Q
  let rewriteRhs : Q :=
    -cast (91 / 20 : ℚ) * qbar ^ 3 - cast (57 / 8 : ℚ) * qbar ^ 2 -
      cast (91 / 20 : ℚ) * qbar - 1
  (Ideal.Quotient.mk I p = 0) ∧
    qbar ^ 4 = rewriteRhs ∧
    qbar ^ 5 = qbar * rewriteRhs ∧
    qbar ^ 5 = rewriteRhs * qbar ∧
    qbar * rewriteRhs = rewriteRhs * qbar ∧
    (∀ n : ℕ, ∃ c₀ c₁ c₂ c₃ : ℚ,
      qbar ^ n = cast c₀ + cast c₁ * qbar + cast c₂ * qbar ^ 2 +
        cast c₃ * qbar ^ 3) ∧
    (40 : ℚ) ≠ 0 ∧
    qInvBar =
      -cast (91 / 20 : ℚ) - cast (57 / 8 : ℚ) * qbar -
        cast (91 / 20 : ℚ) * qbar ^ 2 - qbar ^ 3 ∧
    (∀ n : ℤ, ∃ c₀ c₁ c₂ c₃ : ℚ,
      Ideal.Quotient.mk I (LaurentPolynomial.T n) =
        cast c₀ + cast c₁ * qbar + cast c₂ * qbar ^ 2 +
          cast c₃ * qbar ^ 3)

end MathlibPlus.Open.Algebra.Claim50755
