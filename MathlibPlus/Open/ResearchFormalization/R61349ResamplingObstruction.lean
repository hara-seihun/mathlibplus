import MathlibPlus.Open.ResearchFormalization.Claim51653_51654
import MathlibPlus.Open.ResearchFormalization.OracleAreaShapleyClaim61241

namespace MathlibPlus.Open.ResearchFormalization.R61349ResamplingObstruction

open MathlibPlus.Open.ResearchFormalization.R3867
open MathlibPlus.Open.ResearchFormalization.OracleAreaShapleyClaim61241

noncomputable section

/-- Claim 61349: the explicit per-query resampling policy for two depth-two
components has area 67/32, while the unrestricted Bellman minimum is 13/8. -/
def perQueryResamplingObstruction_claim61349 : Prop :=
  let tree₁ : LevelTree 4 :=
    .query 0 1
      (.query 2 2 (.leaf (-1)) (.leaf 1))
      (.query 1 2 (.leaf 1) (.leaf (-1)))
  let tree₂ : LevelTree 4 :=
    .query 3 1
      (.query 2 2 (.leaf (-1)) (.leaf 1))
      (.query 1 2 (.leaf 1) (.leaf (-1)))
  let weight : Fin 2 → ℝ := fun _ => 1 / 2
  let component : Fin 2 → LevelTree 4 := ![tree₁, tree₂]
  let target : RademacherAssignment 4 → ℝ := fun x =>
    ∑ j : Fin 2, weight j * (component j).evaluate x
  let firstUnresolved : PartialAssignment 4 →
      List (Fin 4 × ℕ) → Option (Fin 4) :=
    fun h path =>
      path.find? (fun q => (h q.1).isNone) |>.map Prod.fst
  let actionMass : PartialAssignment 4 → Fin 4 → ℝ := fun h i =>
    ∑ j : Fin 2,
      weight j *
        ((completions h).filter (fun x =>
          firstUnresolved h ((component j).queryPath x) = some i)).card /
        (completions h).card
  let activeMass : PartialAssignment 4 → ℝ := fun h =>
    ∑ i : Fin 4, actionMass h i
  let actionProbability : PartialAssignment 4 → Fin 4 → ℝ := fun h i =>
    if activeMass h = 0 then 0 else actionMass h i / activeMass h
  let rec policyAux : ℕ → PartialAssignment 4 → ℝ
    | 0, _ => 0
    | k + 1, h =>
        if conditionalVariance h target = 0 then 0 else
          conditionalVariance h target +
            ∑ i : Fin 4, actionProbability h i *
              (policyAux k (partialUpdate h i false) +
                policyAux k (partialUpdate h i true)) / 2
  let policyArea : ℝ :=
    policyAux 4 (emptyPartialAssignment : PartialAssignment 4)
  let minimumBellmanArea : ℝ := minimumArea target
  (∀ j : Fin 2, weight j = 1 / 2) ∧
    (∀ h : PartialAssignment 4, ∀ i : Fin 4,
      actionProbability h i > 0 → h i = none) ∧
    (∀ h : PartialAssignment 4,
      conditionalVariance h target = 0 → policyAux 4 h = 0) ∧
    policyArea = 67 / 32 ∧
    67 / 32 > 2 ∧
    minimumBellmanArea = 13 / 8 ∧
    minimumBellmanArea < 2

end

end MathlibPlus.Open.ResearchFormalization.R61349ResamplingObstruction
