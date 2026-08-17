import MathlibPlus.Open.ResearchFormalization.R1203.Claim41973

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203

def claim32200 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      MathlibPlus.Open.Research.elementaryAbelianSylow p V →
      matchingScalarAction (rho := rho) p omega V →
      ∀ (W : Type*) [AddCommGroup W]
        [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
        [DistribMulAction (eGroup A rho) W],
        Module.finrank (ZMod p) W = 1 →
        matchingModule (p := p) (omega := omega) (A := A) (rho := rho) W →
        ∀ (L : Subgroup (eGroup A rho)) (z : L → W),
          subgroupCocycle (p := p) L z →
          ∃ f : eGroup A rho → W,
            vectorCocycle (p := p) f ∧ ∀ h : L, f h = z h

end MathlibPlus.Open.ResearchFormalization.R1203
