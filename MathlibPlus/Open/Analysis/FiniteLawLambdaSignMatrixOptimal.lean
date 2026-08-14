import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The Boolean cube with `n` coordinate positions. -/
def Cube (n : ℕ) := Fin n → Fin 2

/-- A sign row is a real-valued row on the Boolean cube. -/
def SignRow (n : ℕ) := Cube n → ℝ

/-- The coordinate sign row `T_i`. -/
def coordinateSign (n : ℕ) (i : Fin n) : SignRow n :=
  fun x => if x i = 1 then 1 else -1

/-- The mass prescribed for coordinate `i`. -/
def signMass (n : ℕ) (i : Fin n) : ℝ :=
  (2 : ℝ) ^ i.val / ((2 : ℝ) ^ n - 1)

/-- A finite law represented by finitely many indexed sign rows and their masses. -/
structure SignLaw (n : ℕ) (ι : Type*) where
  row : ι → SignRow n
  mass : ι → ℝ

/-- The indexed law has nonnegative masses summing to one. -/
def IsProbabilityLaw {n : ℕ} {ι : Type*} [Fintype ι]
    (law : SignLaw n ι) : Prop :=
  (∀ i, 0 ≤ law.mass i) ∧ ∑ i, law.mass i = 1

/-- Every row of the law takes only the two sign values. -/
def IsSignRow {n : ℕ} (row : SignRow n) : Prop :=
  ∀ x, row x = 1 ∨ row x = -1

/-- All rows in a law are sign rows. -/
def IsSignLaw {n : ℕ} {ι : Type*} (law : SignLaw n ι) : Prop :=
  ∀ i, IsSignRow (law.row i)

/-- The weighted row average of a finite law. -/
def weightedRowAverage {n : ℕ} {ι : Type*} [Fintype ι]
    (law : SignLaw n ι) : Cube n → ℝ :=
  fun x => ∑ i, law.mass i * law.row i x

/-- The explicitly prescribed law on the `n` coordinate sign rows. -/
def canonicalSignLaw (n : ℕ) : SignLaw n (Fin n) where
  row := coordinateSign n
  mass := signMass n

/-- The explicitly prescribed weighted average. -/
def canonicalMu (n : ℕ) : Cube n → ℝ :=
  fun x => ∑ i, signMass n i * coordinateSign n i x

/-- A finite deterministic adaptive coordinate-reveal decision tree. -/
inductive RevealTree (n : ℕ) where
  | leaf (value : ℝ)
  | query (coordinate : Fin n)
      (zeroBranch : RevealTree n) (oneBranch : RevealTree n)

namespace RevealTree

/-- The exact output of a decision tree on an input. -/
def evaluate {n : ℕ} : RevealTree n → Cube n → ℝ
  | .leaf value, _ => value
  | .query coordinate zeroBranch oneBranch, x =>
      if x coordinate = 1 then evaluate oneBranch x else evaluate zeroBranch x

/-- The coordinates queried on a particular input path. -/
def queried {n : ℕ} : RevealTree n → Cube n → Finset (Fin n)
  | .leaf _, _ => ∅
  | .query coordinate zeroBranch oneBranch, x =>
      insert coordinate
        (queried (if x coordinate = 1 then oneBranch else zeroBranch) x)
  termination_by tree => sizeOf tree
  decreasing_by
    split <;> simp_wf <;> omega

/-- Every coordinate appearing below a query is fresh on either branch. -/
def possibleQueries {n : ℕ} : RevealTree n → Finset (Fin n)
  | .leaf _ => ∅
  | .query coordinate zeroBranch oneBranch =>
      insert coordinate (possibleQueries zeroBranch ∪ possibleQueries oneBranch)

/-- The tree never queries one coordinate twice on a path. -/
def NoRepeatedQueries {n : ℕ} : RevealTree n → Prop
  | .leaf _ => True
  | .query coordinate zeroBranch oneBranch =>
      coordinate ∉ possibleQueries zeroBranch ∧
      coordinate ∉ possibleQueries oneBranch ∧
      NoRepeatedQueries zeroBranch ∧
      NoRepeatedQueries oneBranch

end RevealTree

/-- A coordinate-reveal policy is a deterministic tree with no repeated query. -/
structure RevealPolicy (n : ℕ) where
  tree : RevealTree n
  noRepeated : RevealTree.NoRepeatedQueries tree

/-- The policy computes a target exactly on every cube input. -/
def Computes {n : ℕ} (policy : RevealPolicy n) (target : Cube n → ℝ) : Prop :=
  ∀ x, RevealTree.evaluate policy.tree x = target x

/-- The policy reveals every coordinate on every input path. -/
def RevealsEveryCoordinate {n : ℕ} (policy : RevealPolicy n) : Prop :=
  ∀ x, RevealTree.queried policy.tree x = Finset.univ

/-- Number of distinct sign rows carrying strictly positive mass. -/
noncomputable def positiveSupportCard {n : ℕ} {ι : Type*} [Fintype ι]
    (law : SignLaw n ι) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun i => 0 < law.mass i)).image law.row).card

/--
For every `n ≥ 1`, the prescribed sign law has an injective weighted average,
any exact deterministic adaptive computation of that average reads every
coordinate on every input, and no finite sign law with injective average has
fewer than `n` distinct positively weighted rows.
-/
def finiteLawLambdaSignMatrixOptimalInjectiveSupport (n : ℕ) : Prop :=
  1 ≤ n →
    (∃ law : SignLaw n (Fin n),
      IsProbabilityLaw law ∧
      IsSignLaw law ∧
      (∀ i, 0 < law.mass i) ∧
      Function.Injective law.row ∧
      law.row = coordinateSign n ∧
      law.mass = signMass n ∧
      weightedRowAverage law = canonicalMu n ∧
      Function.Injective (weightedRowAverage law) ∧
      positiveSupportCard law = n) ∧
    (∀ policy : RevealPolicy n,
      Computes policy (canonicalMu n) →
      RevealsEveryCoordinate policy) ∧
    (∀ (ι : Type*) [Fintype ι] (law : SignLaw n ι),
      IsProbabilityLaw law →
      IsSignLaw law →
      Function.Injective (weightedRowAverage law) →
      n ≤ positiveSupportCard law)

end

end MathlibPlus.Open.Analysis
