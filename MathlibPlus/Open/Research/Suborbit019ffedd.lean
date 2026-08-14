import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedd

/-- Claim 28425: setwise fixation of every suborbit by a base-point fixer. -/
def setwiseSuborbitFixation_28425
    {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω))
    (α : Ω)
    (q : Equiv.Perm Ω) : Prop :=
  q α = α ∧
    ∀ y : Ω,
      ∃ g : Equiv.Perm Ω,
        g ∈ G ∧ g α = α ∧ g y = q y

end MathlibPlus.Open.Research.FormalizationBatch019ffedd
