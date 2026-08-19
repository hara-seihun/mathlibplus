import MathlibPlus.Open.ResearchFormalization.R0666Claim29474
import MathlibPlus.Open.ResearchFormalization.R0666Claim29476
import MathlibPlus.Open.ResearchFormalization.R0666Claim29477

open scoped TensorProduct

namespace MathlibPlus.Open.ResearchFormalization.R0666Claim29478

open MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev AF := R0666Claim29477.AF
abbrev AFCoproduct := R0666Claim29477.AFCoproduct
abbrev AFCounit := R0666Claim29477.AFCounit

private def eGroupLike (Δ : AFCoproduct) (ε : AFCounit)
    (k : triangularIndex) (e : AF) : Prop :=
  e.1 = R0666Claim29477.eCoordinate k.1 ∧
    Δ e = e ⊗ₜ[ℚ] e ∧
    ε e = 1

def claim29478 : Prop :=
  ∃ (Δ : AFCoproduct) (ε : AFCounit),
    R0666Claim29477.residualBialgebra Δ ε ∧
      R0666Claim29477.ambientRestriction Δ ε ∧
      R0666Claim29477.afUnitsAreRational ∧
      (∀ k : triangularIndex,
        ∃ e : AF,
          eGroupLike Δ ε k e ∧
            R0666Claim29477.afNonconstant e ∧
            ¬ IsUnit e) ∧
      (∀ S : AF →ₗ[ℚ] AF,
        R0666Claim29474.hopfStructure Δ ε S →
          ∀ k : triangularIndex, ∀ e : AF,
            eGroupLike Δ ε k e → IsUnit e) ∧
      ¬ ∃ S : AF →ₗ[ℚ] AF,
        R0666Claim29474.hopfStructure Δ ε S

end

end MathlibPlus.Open.ResearchFormalization.R0666Claim29478
