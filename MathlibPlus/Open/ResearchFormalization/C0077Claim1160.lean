import MathlibPlus.Open.ResearchFormalization.Claim1159

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim1160

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Claim1159

/-- The stable four-row cup block, its gauge inverse, and its four
area-at-most-two cup coordinates in the shared flagged-minor carrier. -/
def stableLeadingCupBlockAndInverseTransform_claim1160 : Prop :=
  let catalog : Fin 4 → List ℕ :=
    ![[], [1], [2], [1, 1]]
  let catalogSet : Finset (List ℕ) :=
    {[], [1], [2], [1, 1]}
  let available : ℕ → Finset (Fin 4) := fun d =>
    if d = 1 then {0, 1} else if 2 ≤ d then Finset.univ else ∅
  let W : Matrix (Fin 4) (Fin 4) ℝ :=
    ![![1, 0, 0, 0], ![-1, 1, 0, 0], ![0, -1, 1, 0],
      ![0, -1, 0, 1]]
  let S : Matrix (Fin 4) (Fin 4) ℝ :=
    ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0],
      ![0, 0, 0, 1]]
  let T : Matrix (Fin 4) (Fin 4) ℝ :=
    ![![1, 0, 0, 0], ![1, -1, 0, 0], ![1, -1, 1, 0],
      ![1, -1, 0, 1]]
  (Finset.univ.image catalog = catalogSet) ∧
    W⁻¹ * S = T ∧
    (∀ i j : Fin 4, i < j → W i j = 0) ∧
    (∀ d : ℕ, 1 ≤ d →
      (d = 1 →
        available d = ({0, 1} : Finset (Fin 4)) ∧
          (available d).image catalog = ({[], [1]} : Finset (List ℕ))) ∧
      (2 ≤ d →
        available d = (Finset.univ : Finset (Fin 4)) ∧
          (available d).image catalog = catalogSet)) ∧
    (∀ (a : ℝ) (d : ℕ), 1 ≤ d →
      Matrix.mulVec T
          ![principalFlaggedMinor a d, oneFlaggedMinor a d,
            twoFlaggedMinor a d, oneOneFlaggedMinor a d] 0 =
        principalFlaggedMinor a d ∧
      Matrix.mulVec T
          ![principalFlaggedMinor a d, oneFlaggedMinor a d,
            twoFlaggedMinor a d, oneOneFlaggedMinor a d] 1 =
        principalFlaggedMinor a d - oneFlaggedMinor a d) ∧
    (∀ (a : ℝ) (d : ℕ), 2 ≤ d →
      Matrix.mulVec T
          ![principalFlaggedMinor a d, oneFlaggedMinor a d,
            twoFlaggedMinor a d, oneOneFlaggedMinor a d] =
        ![principalFlaggedMinor a d,
          principalFlaggedMinor a d - oneFlaggedMinor a d,
          principalFlaggedMinor a d - oneFlaggedMinor a d + twoFlaggedMinor a d,
          principalFlaggedMinor a d - oneFlaggedMinor a d +
            oneOneFlaggedMinor a d])

end

end MathlibPlus.Open.ResearchFormalization.Claim1160
