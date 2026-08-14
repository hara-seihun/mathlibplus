import Mathlib

namespace MathlibPlus.Open.CommunicationDeficit

/-- The two signs occurring in a sign matrix. -/
abbrev Sign := Fin 2

namespace Sign

/-- The negative and positive elements of `{−1, 1}`. -/
def neg : Sign := 0

def pos : Sign := 1

/-- The real value of a sign. -/
def value (s : Sign) : ℝ := if s = neg then -1 else 1

end Sign

/-- An oracle in `{−1, 1}^I`. -/
abbrev Oracle (I : Type*) := I → Sign

/-- A deterministic coordinate decision tree.  A negative oracle answer takes
    the left branch and a positive answer takes the right branch. -/
inductive DecisionTree (I : Type*) where
  | leaf : Sign → DecisionTree I
  | query : I → DecisionTree I → DecisionTree I → DecisionTree I

namespace DecisionTree

/-- The sign output by a decision tree on an oracle. -/
def evaluate : DecisionTree I → Oracle I → Sign
  | .leaf s, _ => s
  | .query i left right, oracle =>
      if oracle i = Sign.neg then evaluate left oracle else evaluate right oracle

/-- The coordinates queried somewhere in a tree. -/
def queried [DecidableEq I] : DecisionTree I → Finset I
  | .leaf _ => ∅
  | .query i left right => insert i (queried left ∪ queried right)

/-- No coordinate is queried twice on any root-to-leaf path. -/
def Legal [DecidableEq I] : DecisionTree I → Prop
  | .leaf _ => True
  | .query i left right =>
      i ∉ queried left ∧ i ∉ queried right ∧ Legal left ∧ Legal right

/-- The number of queries made on an oracle. -/
def stoppingDepth : DecisionTree I → Oracle I → ℕ
  | .leaf _, _ => 0
  | .query i left right, oracle =>
      Nat.succ <|
        if oracle i = Sign.neg then stoppingDepth left oracle else stoppingDepth right oracle

end DecisionTree

/-- A finitely supported probability distribution written with real weights. -/
structure ProbabilityDistribution (C : Type*) [Fintype C] where
  weight : C → ℝ
  nonnegative : ∀ c, 0 ≤ weight c
  total : ∑ c, weight c = 1

section Quantities

variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]

/-- The expected stopping depth at a fixed oracle. -/
def expectedDepth (p : ProbabilityDistribution C)
    (trees : C → DecisionTree I) (oracle : Oracle I) : ℝ :=
  ∑ c, p.weight c * (trees c).stoppingDepth oracle

/-- The signed mass of all rows at a fixed oracle. -/
def fullMean (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign) (oracle : Oracle I) : ℝ :=
  ∑ c, p.weight c * Sign.value (matrix (c, oracle))

/-- The signed mass of rows stopped by round `m`. -/
def stoppedMean (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign) (trees : C → DecisionTree I)
    (oracle : Oracle I) (m : ℕ) : ℝ :=
  Finset.sum (Finset.univ.filter (fun c => (trees c).stoppingDepth oracle ≤ m))
    (fun c => p.weight c * Sign.value (matrix (c, oracle)))

/-- The surviving positive mass at round `m`. -/
def positiveMass (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign) (trees : C → DecisionTree I)
    (oracle : Oracle I) (m : ℕ) : ℝ :=
  Finset.sum (Finset.univ.filter
      (fun c => (trees c).stoppingDepth oracle > m ∧ matrix (c, oracle) = Sign.pos))
    (fun c => p.weight c)

/-- The surviving negative mass at round `m`. -/
def negativeMass (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign) (trees : C → DecisionTree I)
    (oracle : Oracle I) (m : ℕ) : ℝ :=
  Finset.sum (Finset.univ.filter
      (fun c => (trees c).stoppingDepth oracle > m ∧ matrix (c, oracle) = Sign.neg))
    (fun c => p.weight c)

/-- The unresolved mass `q_m = a_m + b_m`. -/
def unresolvedMass (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign) (trees : C → DecisionTree I)
    (oracle : Oracle I) (m : ℕ) : ℝ :=
  positiveMass p matrix trees oracle m + negativeMass p matrix trees oracle m

/-- The absolute mean deficit `e_m(O)`. -/
def meanDeficit (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign) (trees : C → DecisionTree I)
    (oracle : Oracle I) (m : ℕ) : ℝ :=
  |fullMean p matrix oracle - stoppedMean p matrix trees oracle m|

end Quantities

/--
The exact communication-deficit identity and its two consequences for a finite
sign matrix sampled by a distribution and evaluated by legal coordinate trees.
The declaration is intentionally open: it records the full mathematical claim
without supplying a proof.
-/
def exactCommunicationDeficit
    {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
    (k : ℕ) (p : ProbabilityDistribution C)
    (matrix : C × Oracle I → Sign)
    (trees : C → DecisionTree I)
    (oracle : Oracle I)
    (hcomputes : ∀ c ω, (trees c).evaluate ω = matrix (c, ω))
    (hlegal : ∀ c, (trees c).Legal)
    (hdepth : ∀ c, (trees c).stoppingDepth oracle ≤ k) : Prop :=
  let expected := expectedDepth p trees oracle
  let squaredDeficits :=
    Finset.sum (Finset.range k)
      (fun m => (meanDeficit p matrix trees oracle m) ^ 2)
  let identityRhs :=
    Finset.sum (Finset.range k)
      (fun m =>
        (unresolvedMass p matrix trees oracle m) *
            (1 - unresolvedMass p matrix trees oracle m) +
          4 * positiveMass p matrix trees oracle m * negativeMass p matrix trees oracle m)
  (expected - squaredDeficits = identityRhs) ∧
    (squaredDeficits ≤ expected ∧ expected ≤ (k : ℝ)) ∧
    (squaredDeficits = expected ↔
      ∀ m, m < k →
        ((unresolvedMass p matrix trees oracle m = 0 ∨
            unresolvedMass p matrix trees oracle m = 1) ∧
          positiveMass p matrix trees oracle m *
              negativeMass p matrix trees oracle m = 0))

end MathlibPlus.Open.CommunicationDeficit
