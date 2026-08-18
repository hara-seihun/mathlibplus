import MathlibPlus.Open.NumberTheory.R1899RoughSieveAndEntropy

namespace MathlibPlus.Open.ResearchFormalization.R1899Claim34776

open MathlibPlus.Open.NumberTheory.R1899

/-- Claim 34776: averaging the exact rough-survivor count over all residues
modulo the primorial gives the CRT rough density. -/
def claim34776_onePointAverageRoughDensity : Prop :=
  ∀ (N z : ℕ),
    let Q := primorialUpTo z
    (Q : ℝ)⁻¹ *
        ∑ t : Fin Q, (roughCount (N := N) t : ℝ) =
      (N : ℝ) * roughDensity Q

end MathlibPlus.Open.ResearchFormalization.R1899Claim34776
