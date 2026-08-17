import MathlibPlus.Open.ResearchFormalization.R1203.Claim41973

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203

/-- The exact carrier-and-action data for a matching scalar module on the
`E(A,3)` semidirect product. -/
def claim32197
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type*) [CommGroup A] [Fintype A]
    (rho : c3 →* MulAut A) (omega : ZMod p)
    (V : Sylow p A)
    (d : ℕ) (W : Type*) [AddCommGroup W]
    [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    [DistribMulAction (eGroup A rho) W] : Prop :=
  Nat.ModEq 3 p 1 ∧
    matchingScalarAction (rho := rho) p omega V ∧
      1 ≤ d ∧
        Module.finrank (ZMod p) W = d ∧
          matchingModule (p := p) (omega := omega)
            (A := A) (rho := rho) W

end MathlibPlus.Open.ResearchFormalization.R1203
