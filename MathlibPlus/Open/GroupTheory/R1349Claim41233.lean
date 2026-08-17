import MathlibPlus.Open.GroupTheory.R1349Claim41244

namespace MathlibPlus.Open.GroupTheory.R1349Claim41233

open MathlibPlus.Open.GroupTheory.R1349Claim41244

/-- In the seven-torsion branch, the commutator subgroup has even coordinates
and surjective alternating coordinate projections. -/
def claim41233 : Prop :=
  ∀ K H : Subgroup Base,
    sevenTorsionSurjectiveProjections K →
      H = ⁅K, K⁆ →
        H ≤ alternatingPower ∧ subdirectAlternatingPower H

end MathlibPlus.Open.GroupTheory.R1349Claim41233
