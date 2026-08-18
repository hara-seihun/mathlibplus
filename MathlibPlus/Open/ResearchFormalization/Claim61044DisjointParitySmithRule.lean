import Mathlib
import MathlibPlus.Open.Combinatorics.Claim59963DecisionTreeProfile

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.DisjointParitySmithRuleClaim61044

noncomputable section

open Classical

abbrev BitCube (I : Type*) := I → Bool
abbrev BitHistory (I : Type*) := I → Option Bool
abbrev Tree (I : Type*) :=
  MathlibPlus.Open.Combinatorics.DecisionTree I

private def bitSign (b : Bool) : ℝ :=
  if b then 1 else -1

private def revealedCoordinates {I : Type*} [Fintype I]
    (h : BitHistory I) : Finset I :=
  Finset.univ.filter (fun i => (h i).isSome)

private def unrevealedCoordinates {I : Type*} [Fintype I]
    (h : BitHistory I) : Finset I :=
  Finset.univ.filter (fun i => h i = none)

private def compatibleHistory {I : Type*}
    (h : BitHistory I) (x : BitCube I) : Prop :=
  ∀ i b, h i = some b → x i = b

private def uniformMass {I : Type*} [Fintype I]
    (_ : BitCube I) : ℝ :=
  1 / (Fintype.card (BitCube I) : ℝ)

private def historyMass {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (h : BitHistory I) : ℝ :=
  ∑ x : BitCube I,
    if compatibleHistory h x then mass x else 0

private def conditionalMean {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  if historyMass mass h = 0 then 0 else
    (∑ x : BitCube I,
      if compatibleHistory h x then mass x * f x else 0) /
      historyMass mass h

private def conditionalVariance {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  if historyMass mass h = 0 then 0 else
    (∑ x : BitCube I,
      if compatibleHistory h x then
        mass x * (f x - conditionalMean mass f h) ^ 2
      else 0) /
      historyMass mass h

private def measurableOnHistory {I : Type*}
    (f : BitCube I → ℝ) (h : BitHistory I) : Prop :=
  ∀ x y, compatibleHistory h x → compatibleHistory h y → f x = f y

private def posteriorVariance {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  if measurableOnHistory f h then 0 else conditionalVariance mass f h

private def observeHistory {I : Type*}
    (h : BitHistory I) (x : BitCube I) (i : I) : BitHistory I :=
  Function.update h i (some (x i))

private def historyAtFrom {I : Type*}
    (policy : BitHistory I → Option I) (h : BitHistory I)
    (x : BitCube I) : ℕ → BitHistory I
  | 0 => h
  | n + 1 =>
      let h' := historyAtFrom policy h x n
      match policy h' with
      | none => h'
      | some i => observeHistory h' x i

private def admissiblePolicy {I : Type*} [Fintype I]
    (f : BitCube I → ℝ) (h : BitHistory I)
    (policy : BitHistory I → Option I) : Prop :=
  (∀ h' i, policy h' = some i → h' i = none) ∧
    (∀ h', measurableOnHistory f h' ↔ policy h' = none) ∧
    (∀ x, ∃ n : Fin (Fintype.card I + 1),
      policy (historyAtFrom policy h x (n : ℕ)) = none)

private def conditionalAverage {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (h : BitHistory I)
    (g : BitCube I → ℝ) : ℝ :=
  if historyMass mass h = 0 then 0 else
    (∑ x : BitCube I,
      if compatibleHistory h x then mass x * g x else 0) /
      historyMass mass h

private def policyRiskFrom {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) (policy : BitHistory I → Option I) : ℝ :=
  ∑ n : Fin (Fintype.card I + 1),
    conditionalAverage mass h
      (fun x => posteriorVariance mass f
        (historyAtFrom policy h x (n : ℕ)))

private def optimalRisk {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  sInf {r : ℝ |
    ∃ policy : BitHistory I → Option I,
      admissiblePolicy f h policy ∧
      r = policyRiskFrom mass f h policy}

private def finiteMinimum {I : Type*}
    (s : Finset I) (g : I → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ i, i ∈ s ∧ r = g i}

private def parityCharacter {I : Type*}
    (S : Finset I) (x : BitCube I) : ℝ :=
  S.prod (fun i => bitSign (x i))

private def parityTarget {I : Type*} {m : ℕ}
    (c : ℝ) (a : Fin m → ℝ) (supports : Fin m → Finset I)
    (x : BitCube I) : ℝ :=
  c + ∑ j : Fin m, a j * parityCharacter (supports j) x

private def activeIndices {I : Type*} [Fintype I] {m : ℕ}
    (supports : Fin m → Finset I) (h : BitHistory I) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ¬ supports j ⊆ revealedCoordinates h)

private def remainingCount {I : Type*} [Fintype I] {m : ℕ}
    (supports : Fin m → Finset I) (h : BitHistory I) (j : Fin m) : ℕ :=
  (supports j \ revealedCoordinates h).card

private def parityWeight {m : ℕ}
    (a : Fin m → ℝ) (j : Fin m) : ℝ :=
  (a j) ^ 2

private def smithOrder {I : Type*} [Fintype I] {m q : ℕ}
    (supports : Fin m → Finset I) (a : Fin m → ℝ)
    (h : BitHistory I) (π : Fin q → Fin m) : Prop :=
  q = (activeIndices supports h).card ∧
    (∀ r, π r ∈ activeIndices supports h) ∧
    (∀ j, j ∈ activeIndices supports h → ∃ r, π r = j) ∧
    Function.Injective π ∧
    (∀ r s, r.val < s.val →
      parityWeight a (π s) *
          (remainingCount supports h (π r) : ℝ) ≤
        parityWeight a (π r) *
          (remainingCount supports h (π s) : ℝ))

private def smithPrefixCount {I : Type*} [Fintype I] {m q : ℕ}
    (supports : Fin m → Finset I) (h : BitHistory I)
    (π : Fin q → Fin m) (r : Fin q) : ℝ :=
  ∑ s : Fin q,
    if s ≤ r then (remainingCount supports h (π s) : ℝ) else 0

private def smithCost {I : Type*} [Fintype I] {m q : ℕ}
    (supports : Fin m → Finset I) (a : Fin m → ℝ)
    (h : BitHistory I) (π : Fin q → Fin m) : ℝ :=
  ∑ r : Fin q,
    parityWeight a (π r) * smithPrefixCount supports h π r

private def smithPotential {I : Type*} [Fintype I] {m : ℕ}
    (supports : Fin m → Finset I) (a : Fin m → ℝ)
    (h : BitHistory I) : ℝ :=
  sInf {z : ℝ |
    ∃ (q : ℕ) (π : Fin q → Fin m),
      smithOrder supports a h π ∧ z = smithCost supports a h π}

private def coefficientMass {m : ℕ}
    (a : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, |a j|

private def absRearrangement {m : ℕ}
    (a b : Fin m → ℝ) : Prop :=
  (∃ σ : Fin m → Fin m,
    Function.Bijective σ ∧ ∀ r, b r = |a (σ r)|) ∧
    (∀ r s, r.val < s.val → b s ≤ b r)

private def emptyHistory {I : Type*} : BitHistory I :=
  fun _ => none

private def queryTraceFrom {I : Type*}
    (policy : BitHistory I → Option I) (h : BitHistory I)
    (x : BitCube I) : ℕ → List I
  | 0 => []
  | n + 1 =>
      let previous := queryTraceFrom policy h x n
      match policy (historyAtFrom policy h x n) with
      | none => previous
      | some i => previous ++ [i]

private def queryPosition {I : Type*}
    (policy : BitHistory I → Option I) (h : BitHistory I)
    (x : BitCube I) (i : I) : ℕ :=
  sInf {n : ℕ | i ∈ queryTraceFrom policy h x n}

private def completesParityBlocksInOrder {I : Type*} [Fintype I]
    {m q : ℕ} (supports : Fin m → Finset I)
    (h : BitHistory I) (π : Fin q → Fin m)
    (policy : BitHistory I → Option I) : Prop :=
  (∀ x n i,
    policy (historyAtFrom policy h x n) = some i →
      ∃ r, i ∈ supports (π r)) ∧
  (∀ x i,
    h i = none →
    (∃ r, i ∈ supports (π r)) →
    ∃ n, i ∈ queryTraceFrom policy h x n) ∧
  (∀ x r s i j,
    r.val < s.val →
    h i = none → i ∈ supports (π r) →
    h j = none → j ∈ supports (π s) →
    queryPosition policy h x i < queryPosition policy h x j)

private def targetOfTree {I : Type*}
    (tree : Tree I) (x : BitCube I) : ℝ :=
  tree.eval x

private def signOfCoefficient (a : ℝ) : ℝ :=
  if 0 ≤ a then 1 else -1

private def treeMixtureValue {I : Type*} {m : ℕ}
    (c : ℝ) (a : Fin m → ℝ) (supports : Fin m → Finset I)
    (parityTrees : Fin m → Tree I)
    (plusTree minusTree : Tree I) (x : BitCube I) : ℝ :=
  ∑ j : Fin m, |a j| * targetOfTree (parityTrees j) x +
    ((1 - coefficientMass a + c) / 2) * targetOfTree plusTree x +
    ((1 - coefficientMass a - c) / 2) * targetOfTree minusTree x

private abbrev TreeChoice (m : ℕ) := Fin m ⊕ Fin 2

private def treeChoiceWeight {m : ℕ}
    (c : ℝ) (a : Fin m → ℝ) (z : TreeChoice m) : ℝ :=
  match z with
  | Sum.inl j => |a j|
  | Sum.inr r => if r.val = 0 then
      (1 - coefficientMass a + c) / 2
    else (1 - coefficientMass a - c) / 2

private def treeChoiceTree {I : Type*} {m : ℕ}
    (parityTrees : Fin m → Tree I)
    (plusTree minusTree : Tree I) (z : TreeChoice m) : Tree I :=
  match z with
  | Sum.inl j => parityTrees j
  | Sum.inr r => if r.val = 0 then plusTree else minusTree

private def treeChoiceTarget {I : Type*} {m : ℕ}
    (a : Fin m → ℝ) (supports : Fin m → Finset I)
    (z : TreeChoice m) (x : BitCube I) : ℝ :=
  match z with
  | Sum.inl j =>
      signOfCoefficient (a j) * parityCharacter (supports j) x
  | Sum.inr r => if r.val = 0 then 1 else -1

private def treeMixtureMean {I : Type*} {m : ℕ}
    (c : ℝ) (a : Fin m → ℝ) (supports : Fin m → Finset I)
    (parityTrees : Fin m → Tree I)
    (plusTree minusTree : Tree I) (x : BitCube I) : ℝ :=
  ∑ z : TreeChoice m,
    treeChoiceWeight c a z *
      targetOfTree (treeChoiceTree parityTrees plusTree minusTree z) x

private def explicitRandomizedTreeRepresentation
    {I : Type*} [Fintype I] {m k : ℕ}
    (c : ℝ) (a : Fin m → ℝ) (supports : Fin m → Finset I) : Prop :=
  ∃ (parityTrees : Fin m → Tree I)
    (plusTree minusTree : Tree I),
    (∀ j x,
      targetOfTree (parityTrees j) x =
        signOfCoefficient (a j) * parityCharacter (supports j) x) ∧
    (∀ x, targetOfTree plusTree x = 1) ∧
    (∀ x, targetOfTree minusTree x = -1) ∧
    (∀ j, (parityTrees j).depth ≤ (supports j).card) ∧
    (∀ j, (parityTrees j).depth ≤ k) ∧
    plusTree.depth ≤ k ∧
    minusTree.depth ≤ k ∧
    (∀ j, 0 ≤ |a j|) ∧
    0 ≤ (1 - coefficientMass a + c) / 2 ∧
    0 ≤ (1 - coefficientMass a - c) / 2 ∧
    coefficientMass a +
        (1 - coefficientMass a + c) / 2 +
        (1 - coefficientMass a - c) / 2 = 1 ∧
    (∀ x,
      treeMixtureValue c a supports parityTrees plusTree minusTree x =
        parityTarget c a supports x) ∧
    (∀ z : TreeChoice m, 0 ≤ treeChoiceWeight c a z) ∧
    (∑ z : TreeChoice m, treeChoiceWeight c a z = 1) ∧
    (∀ z : TreeChoice m,
      (treeChoiceTree parityTrees plusTree minusTree z).depth ≤ k) ∧
    (∀ z : TreeChoice m, ∀ x,
      targetOfTree (treeChoiceTree parityTrees plusTree minusTree z) x =
        treeChoiceTarget a supports z x) ∧
    (∀ x,
      treeMixtureMean c a supports parityTrees plusTree minusTree x =
        parityTarget c a supports x)

private def supportsAreNonemptyAndDisjoint {I : Type*} {m : ℕ}
    (supports : Fin m → Finset I) : Prop :=
  (∀ j, (supports j).Nonempty) ∧
    (∀ j s, j ≠ s → Disjoint (supports j) (supports s))

/-- Claim 61044: the exact finite disjoint-parity optimal risk is the
Smith-ordered completion cost at every history; every history with a fresh
coordinate satisfies the Bellman identity and the resulting potential is a
supersolution; the root bounds and the concrete randomized Boolean-tree
mixture are included with their tree evaluation and depth witnesses. -/
def claim61044 : Prop :=
  ∀ (I : Type*) [Fintype I] (m k : ℕ)
    (supports : Fin m → Finset I)
    (a : Fin m → ℝ) (c : ℝ),
    supportsAreNonemptyAndDisjoint supports →
    (∀ j, a j ≠ 0) →
    (∀ j, (supports j).card ≤ k) →
    |c| + coefficientMass a ≤ 1 →
    let target := parityTarget c a supports
    (∀ h,
      optimalRisk uniformMass target h =
        smithPotential supports a h) ∧
    (∀ h,
      (unrevealedCoordinates h).Nonempty →
        optimalRisk uniformMass target h =
          posteriorVariance uniformMass target h +
            finiteMinimum (unrevealedCoordinates h)
              (fun i => conditionalAverage uniformMass h
                (fun x => optimalRisk uniformMass target
                  (observeHistory h x i))) ∧
        smithPotential supports a h =
          posteriorVariance uniformMass target h +
            finiteMinimum (unrevealedCoordinates h)
              (fun i => conditionalAverage uniformMass h
                (fun x => smithPotential supports a
                  (observeHistory h x i))) ∧
        posteriorVariance uniformMass target h +
            finiteMinimum (unrevealedCoordinates h)
              (fun i => conditionalAverage uniformMass h
                (fun x => smithPotential supports a
                  (observeHistory h x i))) ≤
          smithPotential supports a h) ∧
    (∀ h (q : ℕ) (π : Fin q → Fin m),
      smithOrder supports a h π →
        ∃ policy : BitHistory I → Option I,
          admissiblePolicy target h policy ∧
          policyRiskFrom uniformMass target h policy =
            smithPotential supports a h ∧
          completesParityBlocksInOrder supports h π policy) ∧
    (∀ b : Fin m → ℝ, absRearrangement a b →
      smithPotential supports a (emptyHistory) ≤
          (k : ℝ) * ∑ r : Fin m,
            ((r.val + 1 : ℕ) : ℝ) * (b r) ^ 2 ∧
      (k : ℝ) * ∑ r : Fin m,
            ((r.val + 1 : ℕ) : ℝ) * (b r) ^ 2 ≤
          (k : ℝ) / 2 *
            ((coefficientMass a) ^ 2 + ∑ r : Fin m, (b r) ^ 2) ∧
      (k : ℝ) / 2 *
            ((coefficientMass a) ^ 2 + ∑ r : Fin m, (b r) ^ 2) ≤
          (k : ℝ) * (coefficientMass a) ^ 2 ∧
      (k : ℝ) * (coefficientMass a) ^ 2 ≤ (k : ℝ)) ∧
    explicitRandomizedTreeRepresentation (k := k) c a supports

end

end MathlibPlus.Open.ResearchFormalization.DisjointParitySmithRuleClaim61044
