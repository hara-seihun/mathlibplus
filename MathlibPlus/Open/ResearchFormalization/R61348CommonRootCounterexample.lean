import MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootStrongReserveClaim61225
import MathlibPlus.Open.ResearchFormalization.RademacherArea
import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaCommonOptimalRootSquareDepth

namespace MathlibPlus.Open.ResearchFormalization.R61348CommonRootCounterexample

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootStrongReserveClaim61225
open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaCommonOptimalRootSquareDepth

noncomputable section

/-- Claim 61348: the explicit common-displayed-root mixture has a negative
Bellman atom-area one-step defect. -/
def commonRootACounterexample_claim61348 : Prop :=
  let h : BooleanTable 3 := fun x =>
    if x 1 then ! (x 0) else ! (x 2)
  let h' : BooleanTable 3 := fun x => ! (x 2)
  let signedH : RealTable 3 := signedTable h
  let signedH' : RealTable 3 := signedTable h'
  let target : RealTable 3 := fun x =>
    (9 / 11 : ℝ) * signedH x + (2 / 11 : ℝ) * signedH' x
  let drop : Fin 3 → ℝ := fun i =>
    (9 / 11 : ℝ) *
        (areaValue 3 signedH -
          (areaValue 2 (restrictReal signedH i false) +
            areaValue 2 (restrictReal signedH i true)) / 2) +
      (2 / 11 : ℝ) *
        (areaValue 3 signedH' -
          (areaValue 2 (restrictReal signedH' i false) +
            areaValue 2 (restrictReal signedH' i true)) / 2)
  let hTree : DecisionTree 3 :=
    .query 2
      (.query 1 (.leaf 1)
        (.query 0 (.leaf 1) (.leaf (-1))))
      (.query 1 (.leaf (-1))
        (.query 0 (.leaf 1) (.leaf (-1))))
  let h'Tree : DecisionTree 3 :=
    .query 2 (.leaf 1) (.leaf (-1))
  varianceValue target = 103 / 121 ∧
    noRepeat hTree ∧ (∀ x, hTree.evaluate x = signedH x) ∧ treeDepth hTree ≤ 3 ∧
    (match hTree with | .query i _ _ => i = 2 | .leaf _ => False) ∧
    noRepeat h'Tree ∧ (∀ x, h'Tree.evaluate x = signedH' x) ∧ treeDepth h'Tree ≤ 1 ∧
    (match h'Tree with | .query i _ _ => i = 2 | .leaf _ => False) ∧
    drop 0 = 27 / 44 ∧ drop 1 = 9 / 11 ∧ drop 2 = 35 / 44 ∧
    (∀ i : Fin 3, drop i ≤ 9 / 11) ∧
    varianceValue target = 103 / 121 ∧
    9 / 11 - varianceValue target = -4 / 121 ∧
    9 / 11 - varianceValue target < 0

end

end MathlibPlus.Open.ResearchFormalization.R61348CommonRootCounterexample
