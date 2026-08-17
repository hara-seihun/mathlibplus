import Mathlib
import MathlibPlus.Open.ResearchFormalization.RademacherArea

open scoped BigOperators

namespace MathlibPlus.Open.Probability

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open Classical

abbrev Claim50325Cube (n : ℕ) := Fin n → Bool

/-- The depth-one Boolean atoms: signed literals and the two constants. -/
abbrev Claim50325Atom (n : ℕ) := Bool ⊕ (Fin n × Bool)

abbrev Claim50325Law (n : ℕ) := Claim50325Atom n → ℝ

def claim50325AtomValue {n : ℕ} (a : Claim50325Atom n)
    (x : Claim50325Cube n) : ℝ :=
  match a with
  | Sum.inl positive => if positive then 1 else -1
  | Sum.inr (coordinate, positive) =>
      if positive then rademacherValue (x coordinate)
      else -rademacherValue (x coordinate)

def claim50325ProbabilityLaw {n : ℕ} (law : Claim50325Law n) : Prop :=
  (∀ a, 0 ≤ law a) ∧ ∑ a, law a = 1

def claim50325Barycenter {n : ℕ} (law : Claim50325Law n)
    (x : Claim50325Cube n) : ℝ :=
  ∑ a, law a * claim50325AtomValue a x

def claim50325PPlus {n : ℕ} (law : Claim50325Law n) (i : Fin n) : ℝ :=
  law (Sum.inr (i, true))

def claim50325PMinus {n : ℕ} (law : Claim50325Law n) (i : Fin n) : ℝ :=
  law (Sum.inr (i, false))

def claim50325P {n : ℕ} (law : Claim50325Law n) (i : Fin n) : ℝ :=
  claim50325PPlus law i + claim50325PMinus law i

def claim50325A {n : ℕ} (law : Claim50325Law n) (i : Fin n) : ℝ :=
  claim50325PPlus law i - claim50325PMinus law i

def claim50325R {n : ℕ} (law : Claim50325Law n) : ℝ :=
  ∑ i, claim50325P law i

def claim50325S {n : ℕ} (law : Claim50325Law n) : ℝ :=
  ∑ i, |claim50325A law i|

def claim50325ComputesAtom {n : ℕ} (a : Claim50325Atom n)
    (tree : DecisionTree n) : Prop :=
  ∀ x, tree.evaluate x = claim50325AtomValue a x

def claim50325QueryCount {n : ℕ} :
    DecisionTree n → Claim50325Cube n → ℕ
  | .leaf _, _ => 0
  | .query coordinate ifFalse ifTrue, x =>
      1 + if x coordinate then
        claim50325QueryCount ifTrue x
      else
        claim50325QueryCount ifFalse x

def claim50325ExpectedQueryCount {n : ℕ} (tree : DecisionTree n) : ℝ :=
  ∑ x : Claim50325Cube n,
    (claim50325QueryCount tree x : ℝ) / (2 : ℝ) ^ n

def claim50325ValidPrefix {n : ℕ} (a : Claim50325Atom n)
    (tree : DecisionTree n) : Prop :=
  noRepeat tree ∧ claim50325ComputesAtom a tree

def claim50325QueryCost {n : ℕ} (a : Claim50325Atom n) : ℝ :=
  sInf {c : ℝ |
    ∃ tree : DecisionTree n,
      claim50325ValidPrefix a tree ∧
        c = claim50325ExpectedQueryCount tree}

def claim50325QOptimal {n : ℕ} (a : Claim50325Atom n)
    (tree : DecisionTree n) : Prop :=
  claim50325ValidPrefix a tree ∧
    claim50325ExpectedQueryCount tree = claim50325QueryCost a

def claim50325Cell {n : ℕ} (tree : DecisionTree n)
    (path : List Bool) : Finset (Claim50325Cube n) :=
  Finset.univ.filter (fun x => tree.follows x path)

def claim50325Mean {n : ℕ} (g : Claim50325Cube n → ℝ)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  (∑ x ∈ claim50325Cell tree path, g x) /
    (claim50325Cell tree path).card

def claim50325Variance {n : ℕ} (g : Claim50325Cube n → ℝ)
    (tree : DecisionTree n) (path : List Bool) : ℝ :=
  (∑ x ∈ claim50325Cell tree path,
      (g x - claim50325Mean g tree path) ^ 2) /
    (claim50325Cell tree path).card

def claim50325NodeProbability {n : ℕ} (tree : DecisionTree n)
    (path : List Bool) : ℝ :=
  ((claim50325Cell tree path).card : ℝ) / (2 : ℝ) ^ n

def claim50325PolicyArea {n : ℕ} (g : Claim50325Cube n → ℝ)
    (tree : DecisionTree n) : ℝ :=
  tree.internalPaths.sum (fun path =>
    claim50325NodeProbability tree path * claim50325Variance g tree path)

def claim50325SplicePrefix {n : ℕ} (driverPrefix : DecisionTree n)
    (completion : List Bool → DecisionTree n) : DecisionTree n :=
  let rec go : DecisionTree n → List Bool → DecisionTree n
    | .leaf _, path => completion path
    | .query coordinate ifFalse ifTrue, path =>
        .query coordinate
          (go ifFalse (path ++ [false]))
          (go ifTrue (path ++ [true]))
  go driverPrefix []

def claim50325CompletePolicy {n : ℕ} (a : Claim50325Atom n)
    (u : Claim50325Cube n → ℝ) (driverPrefix : DecisionTree n)
    (completion : List Bool → DecisionTree n) : Prop :=
  claim50325QOptimal a driverPrefix ∧
    noRepeat (claim50325SplicePrefix driverPrefix completion) ∧
    (∀ x,
      (claim50325SplicePrefix driverPrefix completion).evaluate x = u x)

/-- `F_H(u)`: the minimum area of a complete policy whose prefix is a
`q(H)`-optimal determining policy for the driver atom `H`. -/
def claim50325F {n : ℕ} (a : Claim50325Atom n)
    (u : Claim50325Cube n → ℝ) : ℝ :=
  sInf {c : ℝ |
    ∃ driverPrefix : DecisionTree n, ∃ completion : List Bool → DecisionTree n,
      claim50325CompletePolicy a u driverPrefix completion ∧
        c = claim50325PolicyArea u
          (claim50325SplicePrefix driverPrefix completion)}

def claim50325ExpectedF {n : ℕ} (law : Claim50325Law n)
    (u : Claim50325Cube n → ℝ) : ℝ :=
  ∑ a, law a * claim50325F a u

def claim50325ExpectedQ {n : ℕ} (law : Claim50325Law n) : ℝ :=
  ∑ a, law a * claim50325QueryCost a

/-- Claim 50325: the weighted-position estimate for every finite law on
signed literals and constants, including arbitrary sign cancellation and
repeated coordinates, together with its exact stopping comparison. The
atom carrier is depth one, so deeper decision-tree atoms are excluded. -/
def claim50325_signedLiteralStopping : Prop :=
  ∀ (n : ℕ) (law : Claim50325Law n), claim50325ProbabilityLaw law →
    let u := claim50325Barycenter law
    let r := claim50325R law
    let s := claim50325S law
    claim50325ExpectedF law u ≤ s ^ 2 * (1 + r - s) ∧
      s ^ 2 * (1 + r - s) ≤ r ∧
      r = claim50325ExpectedQ law ∧
      claim50325ExpectedF law u ≤ claim50325ExpectedQ law

end

end MathlibPlus.Open.Probability
