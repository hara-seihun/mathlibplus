import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61194

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool

/-- A fresh-coordinate policy removes the queried coordinate in both residual
cubes, so every query of this syntax is fresh by construction. -/
inductive Policy : ℕ → Type
  | leaf {n : ℕ} (value : ℝ) : Policy n
  | query {n : ℕ} (coordinate : Fin (n + 1))
      (ifFalse ifTrue : Policy n) : Policy (n + 1)

def insertBit {n : ℕ} (coordinate : Fin (n + 1)) (value : Bool)
    (x : Cube n) : Cube (n + 1) :=
  Fin.insertNth coordinate value (fun j => x j)

def restrict {n : ℕ} (f : Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) (value : Bool) : Cube n → ℝ :=
  fun x => f (insertBit coordinate value x)

def uniformMean {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, f x) / (Fintype.card (Cube n) : ℝ)

def variance {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  let μ := uniformMean f
  uniformMean (fun x => (f x - μ) ^ 2)

def policyDepth {n : ℕ} : Policy n → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue =>
      1 + max (policyDepth ifFalse) (policyDepth ifTrue)

def policyArea {n : ℕ} : Policy n → (Cube n → ℝ) → ℝ
  | .leaf _, _ => 0
  | .query coordinate ifFalse ifTrue, f =>
      variance f +
        (policyArea ifFalse (restrict f coordinate false) +
          policyArea ifTrue (restrict f coordinate true)) / 2

def policyDetermines {n : ℕ} : Policy n → (Cube n → ℝ) → Prop
  | .leaf value, f => ∀ x, f x = value
  | .query coordinate ifFalse ifTrue, f =>
      policyDetermines ifFalse (restrict f coordinate false) ∧
        policyDetermines ifTrue (restrict f coordinate true)

private def booleanFunction {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

private def legalPolicy {n : ℕ} (f : Cube n → ℝ) (p : Policy n) : Prop :=
  policyDetermines p f

noncomputable def optimalArea {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ p : Policy n, legalPolicy f p ∧ a = policyArea p f}

def branchAverageArea {n : ℕ} (f : Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) : ℝ :=
  (optimalArea (restrict f coordinate false) +
      optimalArea (restrict f coordinate true)) / 2

def decrement {n : ℕ} (f : Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) : ℝ :=
  optimalArea f - branchAverageArea f coordinate

def mixture {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube n → ℝ) : Cube n → ℝ :=
  fun x => ∑ j : Fin m, weight j * component j x

def potential {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube n → ℝ) : ℝ :=
  (∑ j : Fin m,
      weight j * Real.sqrt (optimalArea (component j))) ^ 2

def branchPotential {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) (value : Bool) : ℝ :=
  potential weight (fun j => restrict (component j) coordinate value)

def branchPotentialAverage {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) : ℝ :=
  (branchPotential weight component coordinate false +
      branchPotential weight component coordinate true) / 2

def decrementLoad {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) : ℝ :=
  (∑ j : Fin m,
      weight j * Real.sqrt (decrement (component j) coordinate)) ^ 2

def lawConditions {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube n → ℝ) : Prop :=
  (∀ j, 0 ≤ weight j) ∧
    (∑ j : Fin m, weight j = 1) ∧
    (∀ j, booleanFunction (component j))

def nonconstant {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∃ x y, f x ≠ f y

def optimalFirstCoordinate {n : ℕ} (f : Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)) : Prop :=
  ∀ d : Fin (n + 1),
    branchAverageArea f coordinate ≤ branchAverageArea f d

def treeWitnessDepthAtMost {n : ℕ} (f : Cube n → ℝ) (k : ℕ) : Prop :=
  ∃ p : Policy n, legalPolicy f p ∧ policyDepth p ≤ k

def maximumLoad {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube (n + 1) → ℝ) : ℝ :=
  sSup (Set.range (fun coordinate : Fin (n + 1) =>
    (∑ j : Fin m,
      weight j * Real.sqrt (decrement (component j) coordinate)) ^ 2))

def barycenterConstant {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube n → ℝ) (value : ℝ) : Prop :=
  ∀ x, mixture weight component x = value

def greedyPolicy {m n : ℕ} (weight : Fin m → ℝ)
    (component : Fin m → Cube n → ℝ) : Policy n → Prop
  | .leaf value => barycenterConstant weight component value
  | .query coordinate ifFalse ifTrue =>
      (¬ ∃ value, barycenterConstant weight component value) ∧
        (∀ d,
          (∑ j : Fin m,
            weight j * Real.sqrt (decrement (component j) d)) ^ 2 ≤
            (∑ j : Fin m,
              weight j * Real.sqrt (decrement (component j) coordinate)) ^ 2) ∧
        greedyPolicy weight
          (fun j => restrict (component j) coordinate false) ifFalse ∧
        greedyPolicy weight
          (fun j => restrict (component j) coordinate true) ifTrue

def universalLoadCondition (C : ℝ) : Prop :=
  ∀ (m n : ℕ) (weight : Fin m → ℝ)
    (component : Fin m → Cube (n + 1) → ℝ),
    lawConditions weight component →
      variance (mixture weight component) ≤
        C * maximumLoad weight component

/-- Claim 61194: the fixed-representation square-root potential, its exact
branch decrement, the depth budget, Bellman equality, and the conditional
policy implication are all stated on finite independent Boolean cubes. -/
def squareRootDecrementBound_claim61194 : Prop :=
  ∀ (m n : ℕ)
    (weight : Fin m → ℝ)
    (component : Fin m → Cube (n + 1) → ℝ)
    (coordinate : Fin (n + 1)),
    lawConditions weight component →
      (∀ (f : Cube (n + 1) → ℝ),
        ∀ i : Fin (n + 1), 0 ≤ decrement f i) ∧
      (potential weight component -
          branchPotentialAverage weight component coordinate ≥
        decrementLoad weight component coordinate) ∧
      0 ≤ potential weight component ∧
      0 ≤ potential weight component -
        branchPotentialAverage weight component coordinate ∧
      (∀ k : ℕ,
        (∀ j : Fin m,
          treeWitnessDepthAtMost (component j) k) →
          potential weight component ≤
              ∑ j : Fin m,
                weight j * optimalArea (component j) ∧
            (∑ j : Fin m,
                weight j * optimalArea (component j)) ≤ k) ∧
      (∀ j : Fin m, ∀ i : Fin (n + 1),
        nonconstant (component j) →
          optimalFirstCoordinate (component j) i →
            decrement (component j) i = variance (component j)) ∧
      (∀ C : ℝ,
        universalLoadCondition C →
          ∀ k : ℕ,
            (∀ j : Fin m,
              treeWitnessDepthAtMost (component j) k) →
              ∃ p : Policy (n + 1),
                greedyPolicy weight component p ∧
                  policyDetermines p (mixture weight component) ∧
                  policyArea p (mixture weight component) ≤ C * k)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61194
