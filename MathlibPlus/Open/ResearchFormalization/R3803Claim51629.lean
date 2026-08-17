import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

namespace MathlibPlus.Open.ResearchFormalization.R3803.Claim51629

open scoped BigOperators
open MathlibPlus.Open.OracleAreaOccupation
open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

noncomputable section

private def maskDriver51629 (m : Fin 256) : Driver 3 :=
  fun ω =>
    @ite Sign
      (∃ r : Fin 8,
        ω = orderedConfiguration r ∧ Nat.testBit m.val r.val = true)
      (Classical.propDecidable _)
      positiveSign negativeSign

def displayedLaw51629 : BooleanLaw 3 :=
  [(maskDriver51629 85, (1 / 9 : ℝ)),
    (maskDriver51629 195, (8 / 27 : ℝ)),
    (maskDriver51629 69, (4 / 27 : ℝ)),
    (maskDriver51629 81, (4 / 27 : ℝ)),
    (maskDriver51629 87, (4 / 27 : ℝ)),
    (maskDriver51629 213, (4 / 27 : ℝ))]

def targetBarycentre51629 : Configuration 3 → ℝ :=
  fun ω =>
    (5 / 9 : ℝ) * driverValue (maskDriver51629 85) ω +
      (4 / 9 : ℝ) * driverValue (maskDriver51629 195) ω

def supportMask51629 (i : Fin 6) : Fin 256 :=
  match i.val with
  | 0 => 85
  | 1 => 195
  | 2 => 69
  | 3 => 81
  | 4 => 87
  | _ => 213

def displayedWeight51629 (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => 1 / 9
  | 1 => 8 / 27
  | _ => 4 / 27

def displayedRow51629 (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => -128 / 81
  | 1 => 7 / 9
  | _ => -629 / 324

def starRow51629 (rho : DeterministicPolicy 3)
    (K : Driver 3) : ℝ :=
  directionalMinimum K (maskDriver51629 85) targetBarycentre51629 +
    (2 * policyBilinear rho targetBarycentre51629 (driverValue K) -
      policyArea rho targetBarycentre51629 - qCost (maskDriver51629 85))

def supportStarRow51629 (rho : DeterministicPolicy 3)
    (i : Fin 6) : ℝ :=
  starRow51629 rho (maskDriver51629 (supportMask51629 i))

def truncatedCirculation51629 (rho : DeterministicPolicy 3) : ℝ :=
  ∑ i : Fin 6, displayedWeight51629 i *
    (if i.val = 0 then supportStarRow51629 rho i
     else max 0 (supportStarRow51629 rho i))

def fullCirculation51629 (rho : DeterministicPolicy 3) : ℝ :=
  ∑ i : Fin 6, displayedWeight51629 i * supportStarRow51629 rho i

def affineCoefficients51629 : Fin 9 → ℝ :=
  fun i =>
    match i.val with
    | 0 => -65 / 162
    | 1 => 0
    | 2 => 41 / 72
    | 3 => 0
    | 4 => 0
    | 5 => -5 / 72
    | 6 => 0
    | 7 => 0
    | _ => 175 / 324

def affineValue51629 (c : Fin 9 → ℝ)
    (f : Configuration 3 → ℝ) : ℝ :=
  c 0 + ∑ r : Fin 8, c r.succ * f (orderedConfiguration r)

def claim51629 : Prop :=
  ∃ rho : DeterministicPolicy 3,
    activePolicy (maskDriver51629 85) targetBarycentre51629 rho ∧
      isProbabilityLaw displayedLaw51629 ∧
      lawBarycentre displayedLaw51629 = targetBarycentre51629 ∧
      (∀ i : Fin 6,
        supportStarRow51629 rho i = displayedRow51629 i) ∧
      truncatedCirculation51629 rho = 40 / 729 ∧
      fullCirculation51629 rho = -2396 / 2187 ∧
      (∀ K : Driver 3,
        starRow51629 rho K ≤
          affineValue51629 affineCoefficients51629 (driverValue K)) ∧
      affineValue51629 affineCoefficients51629 targetBarycentre51629 =
        -388 / 729 ∧
      affineValue51629 affineCoefficients51629
          (driverValue (maskDriver51629 85)) =
        starRow51629 rho (maskDriver51629 85) ∧
      affineValue51629 affineCoefficients51629
          (driverValue (maskDriver51629 195)) =
        starRow51629 rho (maskDriver51629 195) ∧
      (∀ law : BooleanLaw 3,
        isProbabilityLaw law →
          lawBarycentre law = targetBarycentre51629 →
            lawExpectation law (starRow51629 rho) ≤ -388 / 729)

end

end MathlibPlus.Open.ResearchFormalization.R3803.Claim51629
