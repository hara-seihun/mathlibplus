import MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

namespace MathlibPlus.Open.ResearchFormalization.R1539Claim37746

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

/-- Normality of a subgroup inside the displayed generated permutation group. -/
def normalIn (X H : Subgroup (Equiv.Perm Omega)) : Prop :=
  ∀ x : X, ∀ h : Equiv.Perm Omega,
    h ∈ H ↔ (x : Equiv.Perm Omega) * h * (x : Equiv.Perm Omega)⁻¹ ∈ H

/-- Conjugacy of two subgroups by an element of the displayed generated group. -/
def conjugatesInside (X H K : Subgroup (Equiv.Perm Omega)) : Prop :=
  ∃ x : X, ∀ h : Equiv.Perm Omega,
    h ∈ H ↔ (x : Equiv.Perm Omega) * h * (x : Equiv.Perm Omega)⁻¹ ∈ K

/-- Claim 37746: the two exact regular copies are distinct normal subgroups of
 their generated image and hence are not conjugate inside it. -/
def claim37746 : Prop :=
  normalIn generatedX H ∧
    normalIn generatedX K ∧
      H ≠ K ∧
        ¬ conjugatesInside generatedX H K

end
end MathlibPlus.Open.ResearchFormalization.R1539Claim37746
