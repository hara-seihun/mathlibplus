import MathlibPlus.Open.ResearchFormalization.Claim1159

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim1152

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Claim1159

private def areaAtMostTwoRows (d : ℕ) : Fin 4 → (Fin d → ℕ) :=
  ![principalRows d, oneRows d, twoRows d, oneOneRows d]

private def flaggedMinorVector (a : ℝ) (d : ℕ) : Fin 4 → ℝ :=
  fun i => flaggedMinorFromRows a (areaAtMostTwoRows d i)

private def stableLeadingBlock : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0], ![-1, 1, 0, 0], ![0, -1, 1, 0],
    ![0, -1, 0, 1]]

private def gaugeSignBlock : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

private def inverseGaugeTransform : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 1, 0],
    ![1, -1, 0, 1]]

private def gaugedCupCoordinates (a : ℝ) (d : ℕ) : Fin 4 → ℝ :=
  Matrix.mulVec inverseGaugeTransform (flaggedMinorVector a d)

private def areaAtMostTwoPartitionIndex : Fin 4 → List ℕ :=
  ![[], [1], [2], [1, 1]]

private def areaAtMostTwoPartitions : Finset (List ℕ) :=
  {[], [1], [2], [1, 1]}

private def availableAreaAtMostTwo (d : ℕ) : Finset (Fin 4) :=
  if d = 1 then {0, 1} else if 2 ≤ d then Finset.univ else ∅

/-- The flagged complete-homogeneous array, its four selected minors, and the
area-at-most-two gauged cup coordinates in the shared setup. -/
def flaggedCompleteHomogeneousArrayAndAreaAtMostTwo_claim1152 : Prop :=
  Matrix.det stableLeadingBlock = 1 ∧
    stableLeadingBlock * inverseGaugeTransform = gaugeSignBlock ∧
    Finset.univ.image areaAtMostTwoPartitionIndex = areaAtMostTwoPartitions ∧
    (∀ (a : ℝ) (d : ℕ),
      flaggedMinorVector a d =
        ![principalFlaggedMinor a d, oneFlaggedMinor a d,
          twoFlaggedMinor a d, oneOneFlaggedMinor a d]) ∧
    (∀ (a : ℝ) (d : ℕ),
      gaugedCupCoordinates a d =
        ![principalFlaggedMinor a d,
          principalFlaggedMinor a d - oneFlaggedMinor a d,
          principalFlaggedMinor a d - oneFlaggedMinor a d + twoFlaggedMinor a d,
          principalFlaggedMinor a d - oneFlaggedMinor a d +
            oneOneFlaggedMinor a d]) ∧
    (∀ d : ℕ, 1 ≤ d →
      (d = 1 →
        availableAreaAtMostTwo d = ({0, 1} : Finset (Fin 4)) ∧
        (availableAreaAtMostTwo d).image areaAtMostTwoPartitionIndex =
          ({[], [1]} : Finset (List ℕ))) ∧
      (2 ≤ d →
        availableAreaAtMostTwo d = (Finset.univ : Finset (Fin 4)) ∧
        (availableAreaAtMostTwo d).image areaAtMostTwoPartitionIndex =
          areaAtMostTwoPartitions))

end

end MathlibPlus.Open.ResearchFormalization.Claim1152
