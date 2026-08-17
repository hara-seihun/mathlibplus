import MathlibPlus.LinearAlgebra.ClaimDefinitions20260811

namespace MathlibPlus.Open.ResearchFormalization.R0153Claim18355

noncomputable section

/-- The finite coefficient Hankel matrix associated with a polynomial. -/
def polynomialHankel (P : Polynomial ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => P.coeff (i.val + j.val)

/-- The squared Euclidean norm of a finite real vector. -/
def finiteNormSq {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (v i) ^ 2

/-- Claim 18355: after the two quotient transports, the conditional Hankel
factorization gives exactly the Finsler square and its nonnegativity. -/
def conditionalHankelFinslerSquare18355 : Prop :=
  ∀ (N : ℕ) (Z Ω : Matrix (Fin N) (Fin N) ℝ)
    (c x h q β : Fin N → ℝ)
    (P R : Polynomial ℝ) (lam : ℝ)
    (L : Matrix (Fin N) (Fin N) ℝ),
    let u : Fin N → ℝ :=
      MathlibPlus.LinearAlgebra.Claim18345.displacementJet N Z x c
    let HP : Matrix (Fin N) (Fin N) ℝ := polynomialHankel P N
    let HR : Matrix (Fin N) (Fin N) ℝ := polynomialHankel R N
    let HD : Matrix (Fin N) (Fin N) ℝ :=
      polynomialHankel (P - (lam : ℝ) • R) N
    (dotProduct h (Matrix.mulVec Ω q) =
          dotProduct u (Matrix.mulVec HP u) ∧
      dotProduct h (Matrix.mulVec Ω β) =
          dotProduct u (Matrix.mulVec HR u) ∧
      HD = L * Matrix.transpose L) →
      dotProduct h (Matrix.mulVec Ω q) -
            lam * dotProduct h (Matrix.mulVec Ω β) =
          finiteNormSq (Matrix.mulVec (Matrix.transpose L) u) ∧
        0 ≤ dotProduct h (Matrix.mulVec Ω q) -
            lam * dotProduct h (Matrix.mulVec Ω β)

end

end MathlibPlus.Open.ResearchFormalization.R0153Claim18355
