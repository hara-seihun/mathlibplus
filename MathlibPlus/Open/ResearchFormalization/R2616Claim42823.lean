import MathlibPlus.Open.Analysis.DyadicMobiusEnergy

namespace MathlibPlus.Open.ResearchFormalization.R2616Claim42823

noncomputable section

/-- The full Möbius critical coordinate `G` from Claim 42823. -/
def G (y : ℝ) : ℝ :=
  Real.exp (-y / 2) *
    MathlibPlus.Open.Analysis.fullMobiusTransform (Real.exp (-y))

/-- The odd-part Möbius critical coordinate `U` from Claim 42823. -/
def U (y : ℝ) : ℝ :=
  Real.exp (-y / 2) *
    MathlibPlus.Open.Analysis.oddMobiusTransform (Real.exp (-y))

/-- The logarithmic translation from Claim 42823. -/
def tau (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => f (y - Real.log 2)

/-- The fixed dyadic scalar `q = 2^(-1/2)` from Claim 42823. -/
def q : ℝ :=
  Real.rpow 2 (-1 / 2 : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.R2616Claim42823
