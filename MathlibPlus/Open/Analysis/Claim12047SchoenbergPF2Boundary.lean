import MathlibPlus.Analysis.Schoenberg

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim12047

open MathlibPlus.Analysis.Schoenberg

def schoenbergPF2Boundary_claim12047 : Prop :=
  let zPlus : ℂ := (-1 : ℂ) + Complex.I * Real.sqrt 3
  let zMinus : ℂ := (-1 : ℂ) - Complex.I * Real.sqrt 3
  (∀ z : ℂ,
      (1 + z / 2 + z ^ 2 / 4 = 0 ↔
        z = zPlus ∨ z = zMinus)) ∧
    |Complex.arg zPlus| = forbiddenSectorAngle 2 2 ∧
      |Complex.arg zMinus| = forbiddenSectorAngle 2 2

end MathlibPlus.Open.Analysis.Claim12047

end
