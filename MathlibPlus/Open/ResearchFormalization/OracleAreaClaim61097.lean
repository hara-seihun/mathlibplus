import MathlibPlus.Open.Probability.ActiveRootMassCharging
import MathlibPlus.Open.Probability.ResearchBatch

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61097

noncomputable section

open MathlibPlus.Open.Probability.ActiveRootMassCharging
open MathlibPlus.Open.Probability.ResearchBatch
open MeasureTheory

/-- A legal decision tree never queries a coordinate already queried on the
same root-to-leaf path. -/
def legalSignTreeFrom {I : Type*} (used : Set I) : SignTree I → Prop
  | .leaf _ => True
  | .query i left right =>
      i ∉ used ∧
        legalSignTreeFrom (insert i used) left ∧
          legalSignTreeFrom (insert i used) right

def legalSignTree {I : Type*} (tree : SignTree I) : Prop :=
  legalSignTreeFrom (∅ : Set I) tree

/-- The two-coordinate parity witness used for sharpness. -/
def twoCoordinateParitySharpness : Prop :=
  let Ω := Cube 2
  let parity : Ω → ℝ := fun x =>
    signReal (x 0) * signReal (x 1)
  let witness : QueryTree 2 :=
    .node 0
      (.node 1 .leaf .leaf)
      (.node 1 .leaf .leaf)
  (∀ t : QueryTree 2,
      valid t →
        complete parity t →
          2 ≤ policyArea parity t) ∧
    valid witness ∧
      complete parity witness ∧
        policyArea parity witness = 2

def pairTrees {I : Type*}
    (tF tH : SignTree I) : Fin 2 → SignTree I :=
  Fin.cases tF (fun _ => tH)

/-- A transcript policy is legal when a nonterminal target cell receives a
fresh coordinate. -/
def legalTranscriptPolicy {I Ω : Type*} {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignTree I)
    (O : I → Ω → Bool) (policy : RevealTranscript I → I) : Prop :=
  ∀ h : RevealTranscript I,
    ¬ constantOnCell (targetValue n p trees O) (transcriptCell O h) →
      policy h ∉ Finsupp.support h

/-- Claim 61097: the two Boolean atoms are supplied with legal depth-two
witness trees as antecedent data, and the resulting fixed mixture target has a
legal stopped policy of root-inclusive area at most two, with the exact parity
sharpness statement. -/
def claim61097_twoAtomDepthTwoOracleArea : Prop :=
  (∀ {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (O : I → Ω → Bool)
      (p : Fin 2 → ℝ)
      (F H : (I → Bool) → Bool),
      independentUniformSigns P O →
        validMixtureWeights p →
          ∀ (tF tH : SignTree I),
            (legalSignTree tF ∧
              tF.depth ≤ 2 ∧
                (∀ x : I → Bool, tF.evaluate x = F x)) →
              (legalSignTree tH ∧
                tH.depth ≤ 2 ∧
                  (∀ x : I → Bool, tH.evaluate x = H x)) →
                ∃ (policy : RevealTranscript I → I),
                  let trees := pairTrees tF tH
                  legalTranscriptPolicy p trees O policy ∧
                    determinesTarget p trees O policy ∧
                      posteriorVarianceArea P p trees O policy ≤ 2) ∧
    twoCoordinateParitySharpness

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61097
