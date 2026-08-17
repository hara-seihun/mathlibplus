import MathlibPlus.Open.ResearchFormalization.R1223QuadraticLift

namespace MathlibPlus.Open.ResearchFormalization.R1223QuadraticLift

noncomputable section

/-- The derivative in the second variable is linear at a direction. -/
def derivativeLinearAt
    (φ : Plane p → Fp p) (u : Plane p) : Prop :=
  ∃ L : Plane p →ₗ[Fp p] Fp p,
    ∀ c : Plane p, L c = phiDerivative φ u c

/-- The displayed solution of `D_u F(c) = F(u)`. -/
def quadraticCorrectionPoint (p : ℕ) (u : Plane p) : Plane p :=
  ![(u 0 - 1) * (2 : Fp p)⁻¹, u 1 * (2 : Fp p)⁻¹]

/-- The coordinate vector `(1,0)` in the plane. -/
def firstPlanePoint (p : ℕ) : Plane p :=
  ![1, 0]

/-- Claim 30306: quiet directions form a subspace, their relative derivatives
are bilinear, the quadratic equation has the displayed unique nonzero-direction
solution, and the correction extends linearly to the ambient plane. -/
def claim30306 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∀ (φ : Plane p → Fp p), φ 0 = 0 →
      ∃ Q : Submodule (Fp p) (Plane p),
        (∀ u : Plane p, u ∈ Q ↔ derivativeLinearAt φ u) ∧
        ∃ B : Q →ₗ[Fp p] (Plane p →ₗ[Fp p] Fp p),
          (∀ (u : Q) (c : Plane p),
            B u c = phiDerivative φ (u : Plane p) c) ∧
          (∀ (u : Plane p), u ≠ 0 →
            quadraticDerivative p u (quadraticCorrectionPoint p u) = quadraticF p u ∧
              ∀ c : Plane p,
                quadraticDerivative p u c = quadraticF p u →
                  c = quadraticCorrectionPoint p u) ∧
          ∃ r : Q →ₗ[Fp p] Fp p,
            (∀ u : Q,
              r u = φ (u : Plane p) - B u (u : Plane p) * (2 : Fp p)⁻¹) ∧
            (∀ u : Q,
              B u (quadraticCorrectionPoint p (u : Plane p)) - φ (u : Plane p) =
                -r u - B u (firstPlanePoint p) * (2 : Fp p)⁻¹) ∧
            ∃ ℓ : Plane p →ₗ[Fp p] Fp p,
              ∀ u : Q,
                ℓ (u : Plane p) =
                  B u (quadraticCorrectionPoint p (u : Plane p)) - φ (u : Plane p)

end
end MathlibPlus.Open.ResearchFormalization.R1223QuadraticLift
