import MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61124

namespace MathlibPlus.Open.ResearchFormalization.Claim49625

open MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61124

/-- The two exact real three-bit Bellman tables, in the canonical row order. -/
noncomputable def uRows49625 : Fin 8 → ℝ :=
  ![1, -5 / 8, 1, -5 / 32, 1, 15 / 32, 29 / 32, -1]

noncomputable def vRows49625 : Fin 8 → ℝ :=
  ![3 / 32, -25 / 32, -1, -25 / 32, 15 / 32, 1 / 2, 15 / 32, -1]

noncomputable def u49625 : RealTable 3 := tableFromRows uRows49625
noncomputable def v49625 : RealTable 3 := tableFromRows vRows49625

noncomputable def chord49625 (p : ℝ) : RealTable 3 :=
  fun x => p * u49625 x + (1 - p) * v49625 x

noncomputable def p49625 : ℝ := 1 / 16

/-- Claim 49625: the canonical Bellman-area carrier realizes the displayed
opposite-face chord obstruction exactly. -/
noncomputable def claim49625_oppositeFaceChordObstruction : Prop :=
  uRows49625 2 = 1 ∧
    vRows49625 2 = -1 ∧
    bellmanArea 3 u49625 = 55577 / 65536 ∧
    bellmanArea 3 v49625 = 59281 / 65536 ∧
    bellmanArea 3 (chord49625 p49625) = 236547 / 262144 ∧
    bellmanArea 3 (chord49625 p49625) -
        p49625 * bellmanArea 3 u49625 -
          (1 - p49625) * bellmanArea 3 v49625 = 349 / 262144 ∧
    0 < (349 : ℝ) / 262144

end MathlibPlus.Open.ResearchFormalization.Claim49625
