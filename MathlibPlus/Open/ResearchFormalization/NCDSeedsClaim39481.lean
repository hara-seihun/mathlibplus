import MathlibPlus.Open.ResearchFormalization.NCDCorner

namespace MathlibPlus.Open.ResearchFormalization.NCDSeedsClaim39481

open MathlibPlus.Open.ResearchFormalization.NCDCorner

noncomputable section

private def quotientMapAB : A →+* B :=
  (algebraMap R B).comp quotientMapA

private def cornerC₂ : B := quotientMapAB c₂
private def cornerT : B := quotientMapAB t
private def seedScale : B := algebraMap ℚ B (2 / 9)

private def coefficientInCorner (f : Fin 11 → A) (i : Fin 11) : B :=
  quotientMapAB (f i)

/-- The raw visible corner row, using the expanded row formula from the
    admitted NCD corner calculation. -/
private def rawCornerRow (f : Fin 11 → A) : B :=
  18 * cornerT * coefficientInCorner f 1 -
      9 * cornerS * coefficientInCorner f 3 -
      3 * cornerT * cornerS * coefficientInCorner f 5 +
      3 * (cornerS ^ 2 - cornerC₂) * coefficientInCorner f 7 +
      cornerT * (cornerS ^ 2 - cornerC₂) * coefficientInCorner f 9

private def visibleState (i : Fin 5) : Fin 11 :=
  ![1, 3, 5, 7, 9] i

private def rawCornerSeed (i : Fin 5) : B :=
  seedScale * rawCornerRow (standardBasis (visibleState i))

/-- Claim 39481: the raw NCD corner seeds on the ordered visible states. -/
def claim39481 : Prop :=
  (fun i : Fin 5 => rawCornerSeed i) =
    ![4 * cornerT,
      -2 * cornerS,
      -(algebraMap ℚ B (2 / 3)) * cornerT * cornerS,
      (algebraMap ℚ B (2 / 3)) * (cornerS ^ 2 - cornerC₂),
      (algebraMap ℚ B (2 / 9)) * cornerT * (cornerS ^ 2 - cornerC₂)]

end
end MathlibPlus.Open.ResearchFormalization.NCDSeedsClaim39481
