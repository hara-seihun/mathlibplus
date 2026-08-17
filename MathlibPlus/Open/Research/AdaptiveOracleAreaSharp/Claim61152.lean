import MathlibPlus.Open.ResearchFormalization.AdaptiveIdentification

namespace MathlibPlus.Open.Research.AdaptiveOracleAreaSharp

open MathlibPlus.Open.ResearchFormalization
open scoped BigOperators

noncomputable section

private abbrev BlockCount (s : ℕ) := 2 ^ s
private abbrev Coordinate (s : ℕ) := Fin (BlockCount s) × Fin s
private abbrev Oracle (s : ℕ) := Coordinate s → Bool
private abbrev Order (s : ℕ) :=
  Equiv.Perm (Fin (BlockCount s)) ×
    (Fin (BlockCount s) → Equiv.Perm (Fin s))

private def blockThen (s : ℕ) :
    List (Coordinate s) →
      adaptiveBinaryDecisionTree (Coordinate s) Bool →
        adaptiveBinaryDecisionTree (Coordinate s) Bool
  | [], _ => .leaf true
  | q :: qs, rest =>
      .query q rest (blockThen s qs rest)

private def tribesTree (s : ℕ) :
    List (Fin (BlockCount s)) →
      (Fin (BlockCount s) → Equiv.Perm (Fin s)) →
        adaptiveBinaryDecisionTree (Coordinate s) Bool
  | [], _ => .leaf false
  | b :: bs, orders =>
      blockThen s
        (List.ofFn (fun j : Fin s => (b, orders b j)))
        (tribesTree s bs orders)

private def treeForOrder (s : ℕ) (o : Order s) :
    adaptiveBinaryDecisionTree (Coordinate s) Bool :=
  tribesTree s (List.ofFn o.1) o.2

private def queryOccurs (s : ℕ) (i : Coordinate s) :
    adaptiveBinaryDecisionTree (Coordinate s) Bool → Oracle s → Bool
  | .leaf _, _ => false
  | .query q whenNegative whenPositive, oracle =>
      if q = i then
        true
      else
        match oracle q with
        | false => queryOccurs s i whenNegative oracle
        | true => queryOccurs s i whenPositive oracle

private def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

private def uniformMean (s : ℕ) (f : Oracle s → ℝ) : ℝ :=
  (Fintype.card (Oracle s) : ℝ)⁻¹ * ∑ ω : Oracle s, f ω

private def uniformEventProbability (s : ℕ)
    (event : Oracle s → Bool) : ℝ :=
  uniformMean s (fun ω => if event ω then 1 else 0)

private def independentUniformRademacher (s : ℕ) : Prop :=
  (∀ i : Coordinate s, ∀ b : Bool,
    uniformEventProbability s (fun ω => if ω i = b then true else false) =
      (1 : ℝ) / 2) ∧
  (∀ x : Oracle s,
    uniformEventProbability s
      (fun ω => if ∀ i : Coordinate s, ω i = x i then true else false) =
      (1 : ℝ) / (2 : ℝ) ^ Fintype.card (Coordinate s))

private def tribesFunction (s : ℕ) (ω : Oracle s) : Bool :=
  if ∃ b : Fin (BlockCount s), ∀ j : Fin s, ω (b, j) then
    true
  else
    false

private def uniformWeight (s : ℕ) (_o : Order s) : ℝ :=
  (Fintype.card (Order s) : ℝ)⁻¹

private def mixtureMean (s : ℕ) (ω : Oracle s) : ℝ :=
  ∑ o : Order s,
    uniformWeight s o *
      signValue (adaptiveEvaluate (treeForOrder s o) ω)

private def fixedTarget (s : ℕ) (ω : Oracle s) : ℝ :=
  signValue (tribesFunction s ω)

private def fullGroupedActiveMass (s : ℕ) (i : Coordinate s) : ℝ :=
  ∑ o : Order s,
    uniformWeight s o *
      uniformMean s (fun ω =>
        if queryOccurs s i (treeForOrder s o) ω then 1 else 0)

private def fixedTargetVariance (s : ℕ) : ℝ :=
  let μ := uniformMean s (fixedTarget s)
  uniformMean s (fun ω => (fixedTarget s ω - μ) ^ 2)

private def directGroupedThresholdStageNoReveal
    (s : ℕ) (alpha : ℝ) : Prop :=
  ∀ i : Coordinate s, fullGroupedActiveMass s i < alpha

/-- Claim 61152: the explicit balanced-tribes mixture of common-depth
shared-coordinate decision trees defeats every direct all-occurrence grouped
active-mass threshold estimate. -/
def balancedTribesObstruction_claim61152 : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ s : ℕ,
      (s : ℝ) > max (2 : ℝ) (8 * C / 3) ∧
      let alpha : ℝ := 2 / (s : ℝ)
      let k : ℕ := BlockCount s * s
      0 < alpha ∧ alpha ≤ 1 ∧
      independentUniformRademacher s ∧
      (∀ o : Order s,
        adaptiveQueryDepth (treeForOrder s o) ≤ k) ∧
      (∀ o : Order s, ∀ ω : Oracle s,
        adaptiveEvaluate (treeForOrder s o) ω = tribesFunction s ω) ∧
      (∀ o : Order s, 0 ≤ uniformWeight s o) ∧
      (∑ o : Order s, uniformWeight s o) = 1 ∧
      (∀ ω : Oracle s, mixtureMean s ω = fixedTarget s ω) ∧
      directGroupedThresholdStageNoReveal s alpha ∧
      fixedTargetVariance s > C * alpha

end

end MathlibPlus.Open.Research.AdaptiveOracleAreaSharp
