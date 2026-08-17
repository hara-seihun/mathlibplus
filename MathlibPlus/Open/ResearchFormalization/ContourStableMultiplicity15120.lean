import MathlibPlus.Open.NewResearch2.RationalHankelClaim15109
import MathlibPlus.Open.ResearchFormalization.MatchingPencilError15118

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalization.ContourStableMultiplicity15120

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankelClaim15109
open MathlibPlus.Open.ResearchFormalization.MatchingPencilError15118

/-- The algebraic multiplicity of the spectrum of a finite matrix in an open set. -/
noncomputable def algebraicMultiplicityInside {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) (inside : Set ℂ) : ℕ :=
  let _ : DecidablePred (fun z : ℂ => z ∈ inside) := Classical.decPred _
  ∑ z ∈ A.charpoly.roots.toFinset,
    if z ∈ inside then A.charpoly.rootMultiplicity z else 0

/-- A contour certificate keeps the actual resolvent inverse and its maximum on
its simple closed boundary, rather than replacing the inverse by entrywise data. -/
def contourResolventInverseCertificate {r : ℕ}
    (Ahat : Matrix (Fin r) (Fin r) ℂ)
    (Γ : SimpleContour) (κhatΓ : ℝ) : Prop :=
  (∀ z : ℂ, z ∈ Γ.curve '' Set.Icc (0 : ℝ) 1 →
    Matrix.det (z • (1 : Matrix (Fin r) (Fin r) ℂ) - Ahat) ≠ 0) ∧
    (∃ z₀ : ℂ,
      z₀ ∈ Γ.curve '' Set.Icc (0 : ℝ) 1 ∧
        κhatΓ = spectralTwoNorm
          ((z₀ • (1 : Matrix (Fin r) (Fin r) ℂ) - Ahat)⁻¹)) ∧
    (∀ z : ℂ, z ∈ Γ.curve '' Set.Icc (0 : ℝ) 1 →
      spectralTwoNorm
          ((z • (1 : Matrix (Fin r) (Fin r) ℂ) - Ahat)⁻¹) ≤ κhatΓ)

/-- Contour-stable total algebraic multiplicity: a certified matching-pencil
perturbation whose error times the maximum boundary resolvent is below one
preserves the total multiplicity in the contour interior. -/
def claim_15120_contour_stable_total_algebraic_multiplicity : Prop :=
  ∀ (r : ℕ) (A Ahat : Matrix (Fin r) (Fin r) ℂ) (eA : ℝ),
    spectralTwoNorm (Ahat - A) ≤ eA →
      ∀ (Γ : SimpleContour) (κhatΓ : ℝ),
        contourResolventInverseCertificate Ahat Γ κhatΓ →
          eA * κhatΓ < 1 →
            algebraicMultiplicityInside A Γ.interior =
              algebraicMultiplicityInside Ahat Γ.interior

end

end MathlibPlus.Open.ResearchFormalization.ContourStableMultiplicity15120
