import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Probability.Claim61232

noncomputable section
open Classical

abbrev Cube (n : ℕ) := Fin n → Bool

/-- The sign associated with a Boolean Rademacher outcome. -/
def rademacherSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- A deterministic coordinate-decision tree on an n-cube. -/
inductive DecisionTree (n : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : Fin n) (negative positive : DecisionTree n)

/-- Worst-case depth of a decision tree. -/
def treeDepth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      max (treeDepth negative) (treeDepth positive) + 1

/-- Evaluation of a deterministic coordinate-decision tree. -/
def treeEvaluate {n : ℕ} : DecisionTree n → Cube n → Bool
  | .leaf value, _ => value
  | .query coordinate negative positive, x =>
      if x coordinate then treeEvaluate positive x else treeEvaluate negative x

/-- Minimum deterministic worst-case coordinate-decision-tree depth. -/
def minimumDecisionDepth {n : ℕ} (h : Cube n → Bool) : ℕ :=
  sInf {d : ℕ | ∃ t : DecisionTree n,
    treeEvaluate t = h ∧ treeDepth t = d}

/-- Finite convex representations by Boolean atoms of depth at most two. -/
def admissibleRepresentation {n : ℕ} (f : Cube n → ℝ)
    (support : Finset (Cube n → Bool))
    (weight : (Cube n → Bool) → ℝ) : Prop :=
  (∀ h ∈ support, 0 ≤ weight h) ∧
  (∑ h ∈ support, weight h = 1) ∧
  (∀ h ∈ support, minimumDecisionDepth h ≤ 2) ∧
  (∀ x, ∑ h ∈ support,
    weight h * rademacherSign (h x) = f x)

/-- The depth-at-most-two Boolean convex hull. -/
def depthTwoHull {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∃ support weight, admissibleRepresentation f support weight

/-- Independently reoptimized mass at depth threshold r. -/
def residualDepthTail (n r : ℕ) (f : Cube n → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ support weight,
    admissibleRepresentation f support weight ∧
      c = ∑ h ∈ support,
        if r ≤ minimumDecisionDepth h then weight h else 0}

/-- The representation-independent squared residual depth-tail potential. -/
def residualDepthPotential (n : ℕ) (f : Cube n → ℝ) : ℝ :=
  residualDepthTail n 1 f ^ 2 + residualDepthTail n 2 f ^ 2

/-- Uniform expectation on the finite Rademacher cube. -/
def cubeMean {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, f x) / (Fintype.card (Cube n) : ℝ)

/-- Uniform variance on the finite Rademacher cube. -/
def cubeVariance {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, (f x - cubeMean f) ^ 2) /
    (Fintype.card (Cube n) : ℝ)

/-- The two depth-two selectors in the admitted four-sign witness. -/
def selectorH : Cube 4 → ℝ := fun x =>
  if x 3 then - rademacherSign (x 1) else rademacherSign (x 0)

def selectorK : Cube 4 → ℝ := fun x =>
  if x 3 then - rademacherSign (x 2) else - rademacherSign (x 1)

/-- The convexly mixed target in the witness. -/
def witnessG : Cube 4 → ℝ := fun x =>
  (3 / 4 : ℝ) * selectorH x + (1 / 4 : ℝ) * selectorK x

/-- Insert a revealed Boolean coordinate into a residual three-cube. -/
def insertCoordinate (i : Fin 4) (b : Bool) (y : Cube 3) : Cube 4 :=
  Fin.insertNth i b y

/-- The residual target after a one-coordinate revelation. -/
def restrictCoordinate (f : Cube 4 → ℝ) (i : Fin 4) (b : Bool) : Cube 3 → ℝ :=
  fun y => f (insertCoordinate i b y)

def oneStepPotentialDrop (i : Fin 4) : ℝ :=
  residualDepthPotential 4 witnessG -
    (residualDepthPotential 3 (restrictCoordinate witnessG i false) +
      residualDepthPotential 3 (restrictCoordinate witnessG i true)) / 2

def maximumOneStepPotentialDrop : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin 4))
    ⟨(0 : Fin 4), Finset.mem_univ 0⟩ oneStepPotentialDrop

/-- A finite policy tree which reveals fresh coordinates along each path. -/
inductive RevealPolicy where
  | stop
  | query (coordinate : Fin 4) (negative positive : RevealPolicy)

def compatible (s : Finset (Fin 4)) (a x : Cube 4) : Prop :=
  ∀ i ∈ s, x i = a i

def conditionalMean (s : Finset (Fin 4)) (a : Cube 4)
    (f : Cube 4 → ℝ) : ℝ :=
  let cell := (Finset.univ : Finset (Cube 4)).filter (compatible s a)
  (∑ x ∈ cell, f x) / (cell.card : ℝ)

def conditionalVariance (s : Finset (Fin 4)) (a : Cube 4)
    (f : Cube 4 → ℝ) : ℝ :=
  let cell := (Finset.univ : Finset (Cube 4)).filter (compatible s a)
  (∑ x ∈ cell, (f x - conditionalMean s a f) ^ 2) /
    (cell.card : ℝ)

def policyArea (s : Finset (Fin 4)) (a : Cube 4)
    (f : Cube 4 → ℝ) : RevealPolicy → ℝ
  | .stop => 0
  | .query i negative positive =>
      conditionalVariance s a f +
        (policyArea (insert i s) (Function.update a i false) f negative +
          policyArea (insert i s) (Function.update a i true) f positive) / 2

def legalPolicy (s : Finset (Fin 4)) : RevealPolicy → Prop
  | .stop => True
  | .query i negative positive =>
      i ∉ s ∧
        legalPolicy (insert i s) negative ∧
        legalPolicy (insert i s) positive

def targetConstantOnCell (s : Finset (Fin 4)) (a : Cube 4)
    (f : Cube 4 → ℝ) : Prop :=
  ∀ x y, compatible s a x → compatible s a y → f x = f y

def policyResolves (s : Finset (Fin 4)) (a : Cube 4)
    (f : Cube 4 → ℝ) : RevealPolicy → Prop
  | .stop => targetConstantOnCell s a f
  | .query i negative positive =>
      policyResolves (insert i s) (Function.update a i false) f negative ∧
      policyResolves (insert i s) (Function.update a i true) f positive

/-- Exact Bellman-optimal root-inclusive posterior-variance area of the
    witness, minimized over finite legal deterministic reveal policies. -/
def bellmanOptimalArea : ℝ :=
  sInf {A : ℝ | ∃ p,
    legalPolicy (∅ : Finset (Fin 4)) p ∧
    policyResolves (∅ : Finset (Fin 4)) (fun _ => false) witnessG p ∧
    A = policyArea (∅ : Finset (Fin 4)) (fun _ => false) witnessG p}

/-- Claim 61232: the separately reoptimized q₁/q₂ potential has the stated
    four-sign witness, a one-step defect larger than every fresh-coordinate
    drop, the universal depth-two hull cap, and exact optimal area 81/64. -/
def claim61232 : Prop :=
  depthTwoHull witnessG ∧
  (∀ i : Fin 4,
    depthTwoHull (restrictCoordinate witnessG i false) ∧
    depthTwoHull (restrictCoordinate witnessG i true)) ∧
  residualDepthTail 4 1 witnessG = 1 ∧
  residualDepthTail 4 2 witnessG = 3 / 4 ∧
  residualDepthPotential 4 witnessG = 25 / 16 ∧
  cubeVariance witnessG = 5 / 8 ∧
  maximumOneStepPotentialDrop ≤ 9 / 16 ∧
  (∀ i : Fin 4, oneStepPotentialDrop i ≤ 9 / 16) ∧
  ¬ (∃ i : Fin 4, cubeVariance witnessG ≤ oneStepPotentialDrop i) ∧
  (9 / 16 : ℝ) < 5 / 8 ∧
  (∀ n : ℕ, ∀ f : Cube n → ℝ,
    depthTwoHull f → residualDepthPotential n f ≤ 2) ∧
  bellmanOptimalArea = 81 / 64 ∧
  bellmanOptimalArea < 2 ∧
  (∃ p,
    legalPolicy (∅ : Finset (Fin 4)) p ∧
    policyResolves (∅ : Finset (Fin 4)) (fun _ => false) witnessG p ∧
    policyArea (∅ : Finset (Fin 4)) (fun _ => false) witnessG p =
      bellmanOptimalArea)

end
end MathlibPlus.Open.Probability.Claim61232
