import MathlibPlus.Open.ResearchFormalization.R1203.Claim41970
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41973

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203Claim41970

noncomputable section

/-- Claim 41971: restriction of the one-dimensional matching scalar cocycle
space from `E(A,3)` to any subgroup is onto under the elementary Sylow-p
hypothesis. -/
def claim41971_scalarCocycleRestrictionSurjective : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.Open.Research.elementaryAbelianSylow p V →
      matchingScalarAction (rho := rho) p omega V →
      ∀ (L : Subgroup (eGroup A rho)) (z : L → ZMod p),
        subgroupCocycle (omega := omega) L z →
        ∃ g : eGroup A rho → ZMod p,
          matchingScalarCocycle (omega := omega) g ∧
            ∀ x : L, g x = z x

end
end MathlibPlus.Open.ResearchFormalization.R1203
