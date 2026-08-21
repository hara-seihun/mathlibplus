-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Open.Research.R1298Charts40145_40146_40148

namespace MathlibPlus.Open.ResearchFormalization.R1298DerivativeGroup

noncomputable section

open MathlibPlus.Open.Research.R1298Charts

/-- The exact derivative subgroup for a canonical chart triple, with the
translation parameter `a` retained in every generator. -/
def derivativeGroup_claim40147
    (i j k : Equiv.Perm V)
    (_hi : canonicalChart i) (_hj : canonicalChart j)
    (_hk : canonicalChart k) : Subgroup (Equiv.Perm V) :=
  Subgroup.closure
    {g | ∃ a : V,
      g = i⁻¹ * (Equiv.addRight (j a)) * k * (Equiv.addRight a)⁻¹}

end

end MathlibPlus.Open.ResearchFormalization.R1298DerivativeGroup
