import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch61150

open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

inductive WitnessCoordinate (n : ℕ) where
  | shared
  | b (j : Fin n)
  | c (j : Fin n)
  | d (j : Fin n)
  deriving DecidableEq, Fintype

structure WitnessOutcome (n : ℕ) where
  a : Bool
  b : Fin n → Bool
  c : Fin n → Bool
  d : Fin n → Bool
  deriving DecidableEq, Fintype

def witnessSignValue (b : Bool) : ℝ :=
  if b then 1 else -1

def witnessOracle {n : ℕ} (ω : WitnessOutcome n) :
    WitnessCoordinate n → Bool
  | .shared => ω.a
  | .b j => ω.b j
  | .c j => ω.c j
  | .d j => ω.d j

def witnessSharedSign {n : ℕ} (ω : WitnessOutcome n) : ℝ :=
  witnessSignValue ω.a

def witnessBSign {n : ℕ} (j : Fin n) (ω : WitnessOutcome n) : ℝ :=
  witnessSignValue (ω.b j)

def witnessCSign {n : ℕ} (j : Fin n) (ω : WitnessOutcome n) : ℝ :=
  witnessSignValue (ω.c j)

def witnessDSign {n : ℕ} (j : Fin n) (ω : WitnessOutcome n) : ℝ :=
  witnessSignValue (ω.d j)

def witnessMajority {n : ℕ} (j : Fin n) (ω : WitnessOutcome n) : ℝ :=
  (witnessBSign j ω + witnessCSign j ω + witnessDSign j ω -
      witnessBSign j ω * witnessCSign j ω * witnessDSign j ω) / 2

def witnessComponent {n : ℕ} (j : Fin n) (ω : WitnessOutcome n) : ℝ :=
  witnessSharedSign ω * witnessMajority j ω

def witnessUniformMean {n : ℕ} (f : WitnessOutcome n → ℝ) : ℝ :=
  (∑ ω : WitnessOutcome n, f ω) /
    (Fintype.card (WitnessOutcome n) : ℝ)

def witnessIndependentUniformRademachers (n : ℕ) : Prop :=
  ∀ (S : Finset (WitnessCoordinate n))
    (x : WitnessCoordinate n → Bool),
    witnessUniformMean (fun ω =>
      if ∀ c ∈ S, witnessOracle ω c = x c then 1 else 0) =
        ((1 : ℝ) / 2) ^ S.card

def witnessMeanComponent {n : ℕ} (j : Fin n) : ℝ :=
  witnessUniformMean (witnessComponent j)

def witnessCovariance {n : ℕ}
    (f g : WitnessOutcome n → ℝ) : ℝ :=
  witnessUniformMean (fun ω =>
    (f ω - witnessUniformMean f) * (g ω - witnessUniformMean g))

def witnessDependsOnShared {n : ℕ}
    (f : WitnessOutcome n → ℝ) : Prop :=
  ∃ ω ω' : WitnessOutcome n,
    ω.a ≠ ω'.a ∧
      (∀ j : Fin n,
        ω.b j = ω'.b j ∧ ω.c j = ω'.c j ∧ ω.d j = ω'.d j) ∧
        f ω ≠ f ω'

inductive WitnessTree (n : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : WitnessCoordinate n)
      (negative positive : WitnessTree n)

def witnessTreeDepth {n : ℕ} : WitnessTree n → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (witnessTreeDepth negative) (witnessTreeDepth positive)

def witnessTreeEvaluate {n : ℕ} : WitnessTree n →
    (WitnessCoordinate n → Bool) → Bool
  | .leaf value, _ => value
  | .query coordinate negative positive, oracle =>
      if oracle coordinate then
        witnessTreeEvaluate positive oracle
      else
        witnessTreeEvaluate negative oracle

def witnessBoolProduct (x y : Bool) : Bool :=
  if x = y then true else false

def witnessMajorityTree {n : ℕ} (j : Fin n) (a : Bool) : WitnessTree n :=
  .query (.b j)
    (.query (.c j)
      (.leaf (witnessBoolProduct a false))
      (.query (.d j)
        (.leaf (witnessBoolProduct a false))
        (.leaf (witnessBoolProduct a true))))
    (.query (.c j)
      (.query (.d j)
        (.leaf (witnessBoolProduct a false))
        (.leaf (witnessBoolProduct a true)))
      (.leaf (witnessBoolProduct a true)))

def witnessComponentTree {n : ℕ} (j : Fin n) : WitnessTree n :=
  .query .shared (witnessMajorityTree j false)
    (witnessMajorityTree j true)

def witnessTreeData (n : ℕ) : Prop :=
  ∀ j : Fin n,
    witnessTreeDepth (witnessComponentTree j) ≤ 4 ∧
      ∀ ω : WitnessOutcome n,
        witnessSignValue
            (witnessTreeEvaluate (witnessComponentTree j)
              (witnessOracle ω)) =
          witnessComponent j ω

def witnessComponentsDistinct (n : ℕ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    witnessComponent i ≠ witnessComponent j

def witnessMixtureTarget {n : ℕ}
    (w : Fin n → ℝ) (ω : WitnessOutcome n) : ℝ :=
  ∑ j : Fin n, w j * witnessComponent j ω

def witnessValidPositiveWeights {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ j : Fin n, 0 < w j) ∧ ∑ j : Fin n, w j = 1

abbrev WitnessTranscript (n : ℕ) :=
  WitnessCoordinate n → Option Bool

def witnessCompatible {n : ℕ}
    (h : WitnessTranscript n) (ω : WitnessOutcome n) : Prop :=
  ∀ c : WitnessCoordinate n,
    match h c with
    | none => True
    | some b => witnessOracle ω c = b

noncomputable def witnessTranscriptCell {n : ℕ}
    (h : WitnessTranscript n) : Finset (WitnessOutcome n) :=
  Finset.univ.filter (fun ω => witnessCompatible h ω)

def witnessCellConstant {n : ℕ}
    (f : WitnessOutcome n → ℝ) (h : WitnessTranscript n) : Prop :=
  ∀ ω ∈ witnessTranscriptCell h, ∀ ω' ∈ witnessTranscriptCell h,
    f ω = f ω'

noncomputable def witnessPosteriorVariance {n : ℕ}
    (f : WitnessOutcome n → ℝ) (h : WitnessTranscript n) : ℝ :=
  if witnessCellConstant f h then 0 else
    let C := witnessTranscriptCell h
    let μ := C.sum f / (C.card : ℝ)
    C.sum (fun ω => (f ω - μ) ^ 2) / (C.card : ℝ)

def witnessFirstFreshQuery {n : ℕ} :
    WitnessTree n → WitnessTranscript n → Option (WitnessCoordinate n)
  | .leaf _, _ => none
  | .query coordinate negative positive, h =>
      match h coordinate with
      | none => some coordinate
      | some true => witnessFirstFreshQuery positive h
      | some false => witnessFirstFreshQuery negative h

def witnessFirstUnresolvedList {n : ℕ}
    (indices : List (Fin n)) (h : WitnessTranscript n) : Option (Fin n) :=
  match indices with
  | [] => none
  | j :: rest =>
      match witnessFirstFreshQuery (witnessComponentTree j) h with
      | some _ => some j
      | none => witnessFirstUnresolvedList rest h

def witnessOrderedIndices {n : ℕ} (order : Fin n ≃ Fin n) : List (Fin n) :=
  (Finset.univ.toList.map order)

def witnessFirstUnresolved {n : ℕ}
    (order : Fin n ≃ Fin n) (h : WitnessTranscript n) : Option (Fin n) :=
  witnessFirstUnresolvedList (witnessOrderedIndices order) h

def witnessSequentialPolicy {n : ℕ} (order : Fin n ≃ Fin n)
    (h : WitnessTranscript n) : WitnessCoordinate n :=
  match witnessFirstUnresolved order h with
  | none => .shared
  | some j =>
      match witnessFirstFreshQuery (witnessComponentTree j) h with
      | none => .shared
      | some c => c

def witnessPolicyStep {n : ℕ}
    (f : WitnessOutcome n → ℝ)
    (policy : WitnessTranscript n → WitnessCoordinate n)
    (h : WitnessTranscript n) (ω : WitnessOutcome n) :
    WitnessTranscript n :=
  if witnessCellConstant f h then h
  else Function.update h (policy h) (some (witnessOracle ω (policy h)))

def witnessPolicyTranscript {n : ℕ}
    (f : WitnessOutcome n → ℝ)
    (policy : WitnessTranscript n → WitnessCoordinate n) :
    ℕ → WitnessOutcome n → WitnessTranscript n
  | 0, _ => fun _ => none
  | m + 1, ω =>
      let h := witnessPolicyTranscript f policy m ω
      witnessPolicyStep f policy h ω

def witnessLegalPolicy {n : ℕ}
    (f : WitnessOutcome n → ℝ)
    (policy : WitnessTranscript n → WitnessCoordinate n) : Prop :=
  ∀ h : WitnessTranscript n,
    ¬ witnessCellConstant f h → h (policy h) = none

def witnessDeterminesTarget {n : ℕ}
    (f : WitnessOutcome n → ℝ)
    (policy : WitnessTranscript n → WitnessCoordinate n) : Prop :=
  ∀ ω : WitnessOutcome n, ∃ m : ℕ,
    witnessCellConstant f (witnessPolicyTranscript f policy m ω)

def witnessPolicyArea {n : ℕ}
    (f : WitnessOutcome n → ℝ)
    (policy : WitnessTranscript n → WitnessCoordinate n) : ℝ :=
  ∑' m : ℕ,
    witnessUniformMean (fun ω =>
      witnessPosteriorVariance f
        (witnessPolicyTranscript f policy m ω))

def witnessSortedOrder {n : ℕ}
    (w : Fin n → ℝ) (order : Fin n ≃ Fin n) : Prop :=
  ∀ i j : Fin n, i ≤ j → w (order j) ≤ w (order i)

def witnessFinitePositiveMixtureBound (n : ℕ) : Prop :=
  ∀ w : Fin n → ℝ,
    witnessValidPositiveWeights w →
      ∃ order : Fin n ≃ Fin n,
        witnessSortedOrder w order ∧
          witnessLegalPolicy (witnessMixtureTarget w)
            (witnessSequentialPolicy order) ∧
          witnessDeterminesTarget (witnessMixtureTarget w)
            (witnessSequentialPolicy order) ∧
          witnessPolicyArea (witnessMixtureTarget w)
            (witnessSequentialPolicy order) ≤ 4

def witnessWalshCharacter {n : ℕ}
    (S : Finset (WitnessCoordinate n)) (ω : WitnessOutcome n) : ℝ :=
  ∏ c ∈ S, witnessSignValue (witnessOracle ω c)

def witnessWalshCoefficient {n : ℕ}
    (f : WitnessOutcome n → ℝ)
    (S : Finset (WitnessCoordinate n)) : ℝ :=
  witnessUniformMean (fun ω => f ω * witnessWalshCharacter S ω)

def witnessNonconstantWalshL1Mass {n : ℕ}
    (f : WitnessOutcome n → ℝ) : ℝ :=
  ∑ S : Finset (WitnessCoordinate n),
    if S.Nonempty then |witnessWalshCoefficient f S| else 0

def witnessABSupport {n : ℕ} (j : Fin n) : Finset (WitnessCoordinate n) :=
  {.shared, .b j}

def witnessACSupport {n : ℕ} (j : Fin n) : Finset (WitnessCoordinate n) :=
  {.shared, .c j}

def witnessADSupport {n : ℕ} (j : Fin n) : Finset (WitnessCoordinate n) :=
  {.shared, .d j}

def witnessABCDSupport {n : ℕ} (j : Fin n) : Finset (WitnessCoordinate n) :=
  {.shared, .b j, .c j, .d j}

def witnessWalshSupportsDistinct {n : ℕ} (j : Fin n) : Prop :=
  witnessABSupport j ≠ witnessACSupport j ∧
    witnessABSupport j ≠ witnessADSupport j ∧
    witnessABSupport j ≠ witnessABCDSupport j ∧
    witnessACSupport j ≠ witnessADSupport j ∧
    witnessACSupport j ≠ witnessABCDSupport j ∧
    witnessADSupport j ≠ witnessABCDSupport j

def witnessComponentWalshExpansion {n : ℕ} (j : Fin n) : Prop :=
  ∀ ω : WitnessOutcome n,
    witnessComponent j ω =
      (1 / 2 : ℝ) * witnessWalshCharacter (witnessABSupport j) ω +
      (1 / 2 : ℝ) * witnessWalshCharacter (witnessACSupport j) ω +
      (1 / 2 : ℝ) * witnessWalshCharacter (witnessADSupport j) ω -
      (1 / 2 : ℝ) * witnessWalshCharacter (witnessABCDSupport j) ω

def witnessSignedWalshParity {n : ℕ}
    (f : WitnessOutcome n → ℝ) : Prop :=
  ∃ S : Finset (WitnessCoordinate n),
    f = witnessWalshCharacter S ∨
      f = fun ω => -witnessWalshCharacter S ω

def witnessComponentWalshData {n : ℕ} (j : Fin n) : Prop :=
  witnessComponentWalshExpansion j ∧
    witnessWalshSupportsDistinct j ∧
    witnessWalshCoefficient (witnessComponent j)
        (witnessABSupport j) = (1 / 2 : ℝ) ∧
    witnessWalshCoefficient (witnessComponent j)
        (witnessACSupport j) = (1 / 2 : ℝ) ∧
    witnessWalshCoefficient (witnessComponent j)
        (witnessADSupport j) = (1 / 2 : ℝ) ∧
    witnessWalshCoefficient (witnessComponent j)
        (witnessABCDSupport j) = -(1 / 2 : ℝ) ∧
    (∀ S : Finset (WitnessCoordinate n),
      S ≠ witnessABSupport j →
        S ≠ witnessACSupport j →
          S ≠ witnessADSupport j →
            S ≠ witnessABCDSupport j →
              witnessWalshCoefficient (witnessComponent j) S = 0) ∧
    ¬ witnessSignedWalshParity (witnessComponent j)

def witnessMixtureWalshClaim (n : ℕ) : Prop :=
  ∀ w : Fin n → ℝ,
    witnessValidPositiveWeights w →
      witnessNonconstantWalshL1Mass (witnessMixtureTarget w) = 2

def claim61150 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    witnessIndependentUniformRademachers n ∧
    (∀ j : Fin n, witnessMeanComponent j = 0) ∧
    (∀ i j : Fin n, i ≠ j →
      witnessCovariance (witnessComponent i) (witnessComponent j) = 0) ∧
    (∀ j : Fin n, witnessDependsOnShared (witnessComponent j)) ∧
    witnessTreeData n ∧
    witnessComponentsDistinct n ∧
    witnessFinitePositiveMixtureBound n ∧
    (∀ j : Fin n, witnessComponentWalshData j) ∧
    witnessMixtureWalshClaim n


end MathlibPlus.Open.ResearchFormalization.Batch61150
