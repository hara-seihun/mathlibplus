import MathlibPlus.Open.ResearchFormalization.R1171Claim41597

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41600

open MathlibPlus.Open.ResearchFormalization.R1171Claim41597

/-- Claim 41600: for the actual generated image of the two concrete regular
copies, internal conjugacy is equivalent to membership of the affine summand
of the derivative module. -/
def claim41600 : Prop :=
  ∀ (f : V → F5), f 0 = 0 →
    ∀ (q : Equiv.Perm Ω),
      (∀ z : Ω, q z = fibreShear f z) →
        (∃ y : (generatedImage q : Type),
          conjugateSubgroup (y : Equiv.Perm Ω) regularCopy = targetCopy q) ↔
          (∃ h : V → F5, h ∈ derivativeModule f ∧
            ∃ a : V →ᵃ[F5] F5,
              ∀ v : V, f v = h v + a v)

end MathlibPlus.Open.ResearchFormalization.R1171Claim41600
