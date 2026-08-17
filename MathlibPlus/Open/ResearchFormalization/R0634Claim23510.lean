import MathlibPlus.Open.Algebra.ConductorRees

namespace MathlibPlus.Open.ResearchFormalization.R0634Claim23510

noncomputable section

open MathlibPlus.Open.Algebra.ConductorRees

abbrev Ambient := MathlibPlus.Open.Algebra.ConductorRees.Ambient
abbrev Conormal := Ideal.Cotangent conductorIdeal

def boundaryMonomial (a b : ℕ) (k : eIndex) : Ambient :=
  MvPolynomial.X sVar ^ b * MvPolynomial.X zVar ^ a *
    MvPolynomial.X (eVar k.1)

def degreeFourteenConormalGenerators : Set Conormal :=
  {c | ∃ (p : conductorIdeal) (a b : ℕ) (k : eIndex),
      a + b + k.1 = 14 ∧
      (p : Ambient) = boundaryMonomial a b k ∧
      c = Ideal.toCotangent conductorIdeal p}

def degreeFourteenConormalPiece : Submodule ℚ Conormal :=
  Submodule.span ℚ degreeFourteenConormalGenerators

def minimalBoundaryGeneratorCount : ℕ :=
  Module.finrank ℚ (degreeFourteenConormalPiece : Type)

/-- The exact weight-fourteen piece of the conormal module K/K^2 has the
binomial dimension and the stated count of minimal boundary generators. -/
def claim_23510 : Prop :=
  minimalBoundaryGeneratorCount = Nat.choose 14 2 ∧
    minimalBoundaryGeneratorCount = 91 ∧
    Nat.choose 14 2 = 91

end

end MathlibPlus.Open.ResearchFormalization.R0634Claim23510
