import MathlibPlus.Open.NewResearch2.RationalHankelClaim15109

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalization.O0265Claim15124

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankelClaim15109

/-- The boundary image of a verified simple closed contour. -/
def contourBoundary15124 (Γ : SimpleContour) : Set ℂ :=
  Γ.curve '' Set.Icc (0 : ℝ) 1

/-- The finite coefficient-error envelope on the nominal denominator. -/
noncomputable def denominatorErrorEnvelope15124
    (D Dhat : Polynomial ℂ) (β : ℕ → ℝ) (Γ : SimpleContour) : ℝ :=
  sSup (Set.image
    (fun z : ℂ =>
      ∑ k ∈ Finset.range (max D.natDegree Dhat.natDegree + 1),
        β k * ‖z‖ ^ k)
    (contourBoundary15124 Γ))

/-- The nominal denominator's boundary minimum. -/
noncomputable def nominalBoundaryMinimum15124
    (Dhat : Polynomial ℂ) (Γ : SimpleContour) : ℝ :=
  sInf (Set.image
    (fun z : ℂ => ‖Dhat.eval z‖)
    (contourBoundary15124 Γ))

/-- Algebraic zero count in the open contour interior. -/
noncomputable def polynomialZeroCountInside15124
    (D : Polynomial ℂ) (Γ : SimpleContour) : ℕ :=
  let _ : DecidablePred (fun z : ℂ => z ∈ Γ.interior) := Classical.decPred _
  ∑ z ∈ D.roots.toFinset,
    if z ∈ Γ.interior then D.rootMultiplicity z else 0

/-- Claim 15124: the coefficient-error Rouché certificate preserves the
algebraic zero count for the exact polynomial denominator on an arbitrary
verified contour. -/
def claim15124 : Prop :=
  ∀ (D Dhat : Polynomial ℂ) (β : ℕ → ℝ) (Γ : SimpleContour),
    (∀ k : ℕ, ‖Dhat.coeff k - D.coeff k‖ ≤ β k) →
      nominalBoundaryMinimum15124 Dhat Γ >
        denominatorErrorEnvelope15124 D Dhat β Γ →
          polynomialZeroCountInside15124 D Γ =
            polynomialZeroCountInside15124 Dhat Γ

end

end MathlibPlus.Open.ResearchFormalization.O0265Claim15124
