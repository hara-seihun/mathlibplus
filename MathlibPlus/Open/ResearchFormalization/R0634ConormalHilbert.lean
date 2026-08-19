import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

open scoped BigOperators
namespace MathlibPlus.Open.ResearchFormalization.R0634Conormal
noncomputable section
open MathlibPlus.Open.ResearchFormalization

abbrev ConductorSubmodule : Submodule ℚ RootRing :=
  conductorIdeal.restrictScalars ℚ

def ConormalSquareAmbient : Submodule ℚ RootRing :=
  (conductorIdeal ^ 2).restrictScalars ℚ

abbrev ConormalAmbient := RootRing ⧸ ConormalSquareAmbient

def Conormal : Submodule ℚ ConormalAmbient :=
  Submodule.map (Submodule.mkQ ConormalSquareAmbient) ConductorSubmodule

def ConductorWeightPiece (n : ℕ) : Submodule ℚ RootRing :=
  ConductorSubmodule ⊓ weightPiece n

def ConormalDegreePiece (n : ℕ) : Submodule ℚ (↥Conormal) :=
  Submodule.comap Conormal.subtype
    (Submodule.map (Submodule.mkQ ConormalSquareAmbient)
      (ConductorWeightPiece n))

def conormalHilbertSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (Module.finrank ℚ (ConormalDegreePiece n) : ℚ))

def claim_23499 : Prop :=
  conormalHilbertSeries =
    PowerSeries.X ^ 2 * (1 - PowerSeries.X)⁻¹ ^ 3

end
end MathlibPlus.Open.ResearchFormalization.R0634Conormal
