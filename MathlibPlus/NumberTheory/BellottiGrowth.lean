import Mathlib

/-!
# Exact Bellotti growth constants

This file formalizes all exact definitions in Record 1 of source record `C-0095`.
The later analytic transfer theorems remain separate claims with their full domains and
are not represented by schematic substitutes here.
-/

namespace MathlibPlus.NumberTheory.BellottiGrowth

/-- Bellotti's exact constant `C = 8.7979`. -/
noncomputable def bellottiC : ℝ := 87979 / 10000

/-- Bellotti's exact constant `D = 132.94357`. -/
noncomputable def bellottiD : ℝ := 13294357 / 100000

/-- The exact transferred amplitude `A_*` from packet `C-0095`. -/
noncomputable def exactGrowthA : ℝ :=
  (bellottiC + 1 + (10 : ℝ) ^ (-80 : ℤ)) /
      Real.rpow (108 * Real.log 10) ((2 : ℝ) / 3) +
    1.569 * bellottiC * Real.rpow bellottiD ((1 : ℝ) / 3)

/-- The exact transferred exponent coefficient `B_*` from packet `C-0095`. -/
noncomputable def exactGrowthB : ℝ :=
  ((2 : ℝ) / 9) * Real.sqrt (3 * bellottiD)

/-- The Vinogradov–Korobov envelope used by packet `C-0095`. -/
noncomputable def vkEnvelope (A B σ t : ℝ) : ℝ :=
  A * Real.rpow |t| (B * Real.rpow (1 - σ) ((3 : ℝ) / 2)) *
    Real.rpow (Real.log |t|) ((2 : ℝ) / 3)

/-- The terminating decimals in the packet are exactly the displayed rational
constants, rather than rounded approximations. -/
theorem bellottiConstants_exact :
    bellottiC = 8.7979 ∧ bellottiD = 132.94357 := by
  norm_num [bellottiC, bellottiD]

end MathlibPlus.NumberTheory.BellottiGrowth
