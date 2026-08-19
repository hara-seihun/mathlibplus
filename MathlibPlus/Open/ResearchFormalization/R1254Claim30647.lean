import MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254_30644

namespace MathlibPlus.Open.ResearchFormalization.R1254

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254

/-- A defect cycle in the exact normalized ternary-cube relation carrier. -/
def defectCycle30647 (r : RepairRelationCarrier_30644) : Prop :=
  r ∈ repairFullRelationGenerators30644

/-- The row-span rank of a defect cycle. -/
def defectCycleRank30647 (r : RepairRelationCarrier_30644) : ℕ :=
  Module.finrank RepairF3_30644
    (Submodule.span RepairF3_30644 (Set.range r))

/-- Claim 30647: in the exact `a=3` normalized cube carrier, every
nonzero-obstruction defect cycle has rank at least five, and rank five is
attained. -/
def claim30647 : Prop :=
  (∀ r : RepairRelationCarrier_30644,
    defectCycle30647 r →
      repairObstruction30644 r ≠ 0 →
        5 ≤ defectCycleRank30647 r) ∧
  (∃ r : RepairRelationCarrier_30644,
    defectCycle30647 r ∧
      repairObstruction30644 r ≠ 0 ∧
        defectCycleRank30647 r = 5)

end
end MathlibPlus.Open.ResearchFormalization.R1254
