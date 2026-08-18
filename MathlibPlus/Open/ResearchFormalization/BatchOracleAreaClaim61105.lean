import MathlibPlus.Open.Analysis.OracleAreaDepthTwoFiveFourths

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchOracleAreaClaim61105

open MeasureTheory
open MathlibPlus.Open.Analysis

private def treeCoordinates {I : Type*} [DecidableEq I] :
    SignDecisionTree I → Finset I
  | .leaf _ => ∅
  | .query i negative positive =>
      insert i (treeCoordinates negative ∪ treeCoordinates positive)

private def treeLegalFrom {I : Type*} [DecidableEq I]
    (seen : Finset I) : SignDecisionTree I → Prop
  | .leaf _ => True
  | .query i negative positive =>
      i ∉ seen ∧
        treeLegalFrom (insert i seen) negative ∧
          treeLegalFrom (insert i seen) positive

private def treeLegal {I : Type*} (tree : SignDecisionTree I) : Prop :=
  letI := Classical.decEq I
  treeLegalFrom ∅ tree

private def finiteDepthTwoLaw {I : Type*} [DecidableEq I]
    {n : ℕ} (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I) : Prop :=
  (∀ j, 0 ≤ p j) ∧
    (∑ j : Fin n, p j = 1) ∧
      (∀ j, treeLegal (trees j) ∧ (trees j).depth ≤ 2)

private abbrev Transcript (I : Type*) := I →₀ Fin 3

private def encodeSign (s : Sign) : Fin 3 :=
  if s = negSign then 1 else 2

private def decodeSign (c : Fin 3) : Sign :=
  if c = 1 then negSign else posSign

private def compatible
    {I : Type*} (h : Transcript I) (O : I → Sign) : Prop :=
  ∀ i, h i ≠ 0 → decodeSign (h i) = O i

private def transcriptCell {I : Type*}
    (h : Transcript I) : Set (I → Sign) :=
  {O | compatible h O}

private def observe {I : Type*} [DecidableEq I]
    (h : Transcript I) (i : I) (s : Sign) : Transcript I :=
  Finsupp.update h i (encodeSign s)

private noncomputable def conditionalMean {I : Type*}
    (P : Measure (I → Sign)) (h : Transcript I)
    (f : (I → Sign) → ℝ) : ℝ :=
  if P (transcriptCell h) = 0 then 0 else
    (∫ O in transcriptCell h, f O ∂P) /
      (P (transcriptCell h)).toReal

private noncomputable def conditionalVariance {I : Type*}
    (P : Measure (I → Sign)) (h : Transcript I)
    (f : (I → Sign) → ℝ) : ℝ :=
  if P (transcriptCell h) = 0 then 0 else
    (∫ O in transcriptCell h,
      (f O - conditionalMean P h f) ^ 2 ∂P) /
      (P (transcriptCell h)).toReal

private noncomputable def atomFunction {I : Type*}
    (tree : SignDecisionTree I) : (I → Sign) → ℝ :=
  fun O => signValue (tree.evaluate O)

private noncomputable def atomLinear {I : Type*}
    (P : Measure (I → Sign)) (h : Transcript I)
    (tree : SignDecisionTree I) (i : I) : ℝ :=
  conditionalMean P h
    (fun O => atomFunction tree O * signValue (O i))

private noncomputable def atomQuadratic {I : Type*}
    (P : Measure (I → Sign)) (h : Transcript I)
    (tree : SignDecisionTree I) (i j : I) : ℝ :=
  conditionalMean P h
    (fun O => atomFunction tree O * signValue (O i) * signValue (O j))

private def freshCoordinates {I : Type*} [DecidableEq I]
    (U : Finset I) (h : Transcript I) : Finset I :=
  U.filter (fun i => h i = 0)

private def unorderedPairs {I : Type*} [DecidableEq I]
    (U : Finset I) : Finset (Finset I) :=
  U.powerset.filter (fun S => S.card = 2)

private noncomputable def pairMass {I : Type*} [DecidableEq I]
    (P : Measure (I → Sign)) (h : Transcript I)
    (tree : SignDecisionTree I) (S : Finset I) : ℝ :=
  (∑ i ∈ S, ∑ j ∈ S.filter (fun j => j ≠ i),
    |atomQuadratic P h tree i j|) / 2

private noncomputable def atomPhi {I : Type*} [DecidableEq I]
    (P : Measure (I → Sign)) (h : Transcript I)
    (U : Finset I) (tree : SignDecisionTree I) : ℝ :=
  conditionalVariance P h (atomFunction tree) +
    ∑ S ∈ unorderedPairs (freshCoordinates U h),
      pairMass P h tree S

private noncomputable def atomS {I : Type*} [DecidableEq I]
    (P : Measure (I → Sign)) (h : Transcript I)
    (U : Finset I) (tree : SignDecisionTree I) (i : I) : ℝ :=
  (atomLinear P h tree i) ^ 2 +
    ∑ j ∈ (freshCoordinates U h).filter (fun j => j ≠ i),
      |atomQuadratic P h tree i j|

private def activeCoordinates {I : Type*} [DecidableEq I]
    {n : ℕ} (trees : Fin n → SignDecisionTree I) : Finset I :=
  (Finset.univ : Finset (Fin n)).biUnion
    (fun j => treeCoordinates (trees j))

private noncomputable def reserveP {I : Type*} [DecidableEq I]
    {n : ℕ} (P : Measure (I → Sign)) (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I)
    (U : Finset I) (h : Transcript I) : ℝ :=
  ∑ j : Fin n, p j * atomPhi P h U (trees j)

private noncomputable def loadL {I : Type*} [DecidableEq I]
    {n : ℕ} (P : Measure (I → Sign)) (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I)
    (U : Finset I) (h : Transcript I) (i : I) : ℝ :=
  ∑ j : Fin n, p j * atomS P h U (trees j) i

private noncomputable def loadM {I : Type*} [DecidableEq I]
    {n : ℕ} (P : Measure (I → Sign)) (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I)
    (U : Finset I) (h : Transcript I) : ℝ :=
  Finset.fold max 0 (fun i => loadL P p trees U h i)
    (freshCoordinates U h)

private noncomputable def targetFunction {I : Type*}
    {n : ℕ} (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I) : (I → Sign) → ℝ :=
  fun O => ∑ j : Fin n, p j * atomFunction (trees j) O

private noncomputable def targetVariance {I : Type*}
    (P : Measure (I → Sign)) {n : ℕ} (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I)
    (h : Transcript I) : ℝ :=
  conditionalVariance P h (targetFunction p trees)

private noncomputable def positivePart (x : ℝ) : ℝ := max x 0

private def positiveSlackPremise {I : Type*} [DecidableEq I]
    {n : ℕ} (P : Measure (I → Sign)) (p : Fin n → ℝ)
    (trees : Fin n → SignDecisionTree I) (U : Finset I) : Prop :=
  ∀ h : Transcript I,
    targetVariance P p trees h > loadM P p trees U h →
      ∃ i ∈ freshCoordinates U h,
        targetVariance P p trees h ≤
          loadL P p trees U h i +
            (positivePart
                (loadM P p trees U (observe h i negSign) -
                  targetVariance P p trees (observe h i negSign)) +
              positivePart
                (loadM P p trees U (observe h i posSign) -
                  targetVariance P p trees (observe h i posSign))) / 2

private noncomputable def policyTranscript {I : Type*}
    [DecidableEq I]
    (policy : Transcript I → Option I) :
    (I → Sign) → ℕ → Transcript I
  | _, 0 => 0
  | O, m + 1 =>
      let h := policyTranscript policy O m
      match policy h with
      | none => h
      | some i => observe h i (O i)

private def policyLegal {I : Type*} [DecidableEq I]
    (policy : Transcript I → Option I) (U : Finset I) : Prop :=
  ∀ h i, policy h = some i → i ∈ freshCoordinates U h

private def targetMeasurableAt {I : Type*}
    (h : Transcript I) (target : (I → Sign) → ℝ) : Prop :=
  ∀ O O', compatible h O → compatible h O' → target O = target O'

private def policyStopsExactly {I : Type*}
    (policy : Transcript I → Option I)
    (target : (I → Sign) → ℝ) : Prop :=
  ∀ h, policy h = none ↔ targetMeasurableAt h target

private noncomputable def policyArea {I : Type*}
    [DecidableEq I] (P : Measure (I → Sign)) {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignDecisionTree I)
    (policy : Transcript I → Option I) : ℝ :=
  ∑' m : ℕ,
    ∫ O,
      conditionalVariance P
        (policyTranscript policy O m)
        (targetFunction p trees) ∂P

/-- Claim 61105: the positive-slack reserve premise for the correctly
    restricted residual Walsh coefficients yields a deterministic legal policy
    with the root-inclusive posterior-variance bound and the atomwise depth-two
    reserve bound. -/
def positiveSlackReserveCertificate_claim61105 : Prop :=
  ∀ (I : Type*) [Countable I],
    letI := Classical.decEq I
    ∀ (P : Measure (I → Sign)) (n : ℕ)
      (p : Fin n → ℝ) (trees : Fin n → SignDecisionTree I),
      IndependentUniformSigns P →
        finiteDepthTwoLaw p trees →
          let U := activeCoordinates trees
          positiveSlackPremise P p trees U →
            ∃ policy : Transcript I → Option I,
              policyLegal policy U ∧
                policyStopsExactly policy (targetFunction p trees) ∧
                policyArea P p trees policy ≤
                  reserveP P p trees U 0 -
                    positivePart
                      (loadM P p trees U 0 -
                        targetVariance P p trees 0) ∧
                reserveP P p trees U 0 -
                    positivePart
                      (loadM P p trees U 0 -
                        targetVariance P p trees 0) ≤
                  reserveP P p trees U 0 ∧
                  reserveP P p trees U 0 ≤ 2

end MathlibPlus.Open.ResearchFormalization.BatchOracleAreaClaim61105
