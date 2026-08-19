import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3728SupportTranslation

noncomputable section

/-- Claim 50189: translating a finite positive offset support transports the
A/B residuals and preserves complementarity at every positive integral
translated start. -/
def translatedComplementarySupport_claim50189 : Prop :=
  ∀ (D : Finset ℕ),
    (∀ d ∈ D, 1 ≤ d) →
      ∀ N : ℤ,
        let A_D : ℚ :=
          ∑ d ∈ D, ((2 : ℚ) ^ d)⁻¹
        let B_D : ℚ :=
          ∑ d ∈ D, (d : ℚ) * ((2 : ℚ) ^ d)⁻¹
        ((N : ℚ) * A_D + B_D = 2) →
          ∀ c : ℕ, 1 ≤ c →
            let D_c : Finset ℕ := D.image (fun d => d + c)
            let A_Dc : ℚ :=
              ∑ d ∈ D_c, ((2 : ℚ) ^ d)⁻¹
            let B_Dc : ℚ :=
              ∑ d ∈ D_c, (d : ℚ) * ((2 : ℚ) ^ d)⁻¹
            let N_c : ℚ :=
              (N : ℚ) - c +
                2 * ((2 : ℚ) ^ c - 1) / A_D
            A_Dc = ((2 : ℚ) ^ c)⁻¹ * A_D ∧
              B_Dc = ((2 : ℚ) ^ c)⁻¹ * (B_D + c * A_D) ∧
              ∀ n_c : ℤ, 0 < n_c →
                (n_c : ℚ) = N_c →
                  (n_c : ℚ) * A_Dc + B_Dc = 2

end

end MathlibPlus.Open.ResearchFormalization.R3728SupportTranslation
