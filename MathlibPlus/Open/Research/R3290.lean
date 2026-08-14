import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.R3290

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev BoolTable (n : ℕ) := Cube n → Bool

inductive DecisionTree (n : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : Fin n) (zeroBranch oneBranch : DecisionTree n)

def evalTree {n : ℕ} : DecisionTree n → Cube n → Bool
  | .leaf value, _ => value
  | .query i zeroBranch oneBranch, x =>
      if x i then evalTree oneBranch x else evalTree zeroBranch x

def depthCost {n : ℕ} : DecisionTree n → Cube n → ℕ
  | .leaf _, _ => 0
  | .query i zeroBranch oneBranch, x =>
      1 + if x i then depthCost oneBranch x else depthCost zeroBranch x

def expectedQueryCost {n : ℕ} (t : DecisionTree n) : ℝ :=
  (∑ x : Cube n, (depthCost t x : ℝ)) / (2 ^ n : ℝ)

def queryCost {n : ℕ} (f : BoolTable n) : ℝ :=
  sInf {c : ℝ | ∃ t : DecisionTree n,
    (∀ x, evalTree t x = f x) ∧ c = expectedQueryCost t}

def restrictTable {n : ℕ} (f : BoolTable n) (i : Fin n) (b : Bool) : BoolTable n :=
  fun x => f (Function.update x i b)

def saving {n : ℕ} (f : BoolTable n) (i : Fin n) : ℝ :=
  queryCost f -
    (queryCost (restrictTable f i false) + queryCost (restrictTable f i true)) / 2

def signValue (b : Bool) : ℝ := if b then 1 else -1

def dataIndex : Bool → Bool → Fin 6
  | false, false => 2
  | false, true => 3
  | true, false => 4
  | true, true => 5

def hTable : BoolTable 6 := fun x => x (dataIndex (x 0) (x 1))

def hReal (x : Cube 6) : ℝ := signValue (hTable x)

def character (S : Finset (Fin 6)) (x : Cube 6) : ℝ :=
  ∏ i ∈ S, signValue (x i)

def fourierCoefficient (f : Cube 6 → ℝ) (S : Finset (Fin 6)) : ℝ :=
  (∑ x : Cube 6, f x * character S x) / (2 ^ 6 : ℝ)

def fourierSupport (f : Cube 6 → ℝ) : Finset (Finset (Fin 6)) :=
  (Finset.univ : Finset (Finset (Fin 6))).filter
    (fun S => fourierCoefficient f S ≠ 0)

def pShare (f : Cube 6 → ℝ) (i : Fin 6) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin 6))).filter (fun S => i ∈ S),
    fourierCoefficient f S ^ 2 / (S.card : ℝ)

def expansionRight (x : Cube 6) : ℝ :=
  (1 / 4 : ℝ) * ∑ u : Bool, ∑ v : Bool,
    signValue (x (dataIndex u v)) *
      (1 + signValue u * signValue (x 0)) *
      (1 + signValue v * signValue (x 1))

def permutedTable (σ : Equiv.Perm (Fin 6)) : BoolTable 6 :=
  fun x => hTable (fun i => x (σ i))

def expectedSaving (i : Fin 6) : ℝ :=
  (∑ σ : Equiv.Perm (Fin 6), saving (permutedTable σ) i) /
    (Nat.factorial 6 : ℝ)

def expectedWeight (S : Finset (Fin 6)) (i : Fin 6) : ℝ :=
  (∑ σ : Equiv.Perm (Fin 6),
      fourierCoefficient (fun x => signValue (permutedTable σ x)) S ^ 2 /
        saving (permutedTable σ) i) / (Nat.factorial 6 : ℝ)

def minimumWeight (S : Finset (Fin 6)) : ℝ :=
  sInf {z : ℝ | ∃ i ∈ S, z = expectedWeight S i}

def orbitMean (x : Cube 6) : ℝ :=
  (∑ σ : Equiv.Perm (Fin 6), signValue (permutedTable σ x)) /
    (Nat.factorial 6 : ℝ)

def meanValue (f : Cube 6 → ℝ) : ℝ :=
  (∑ x : Cube 6, f x) / (2 ^ 6 : ℝ)

def varianceValue (f : Cube 6 → ℝ) : ℝ :=
  ∑ x : Cube 6, (f x - meanValue f) ^ 2 / (2 ^ 6 : ℝ)

def maximumExpectedSaving : ℝ :=
  sSup {z : ℝ | ∃ i : Fin 6, z = expectedSaving i}

def claim47180 : Prop :=
  queryCost hTable = 3 ∧
  saving hTable 0 = 1 ∧ saving hTable 1 = 1 ∧
  (∀ i : Fin 4, saving hTable ⟨i.val + 2, by omega⟩ = 1 / 4) ∧
  (∀ x : Cube 6, hReal x = expansionRight x) ∧
  (fourierSupport hReal).card = 16 ∧
  (∀ S ∈ fourierSupport hReal, |fourierCoefficient hReal S| = 1 / 4) ∧
  pShare hReal 0 = 5 / 24 ∧ pShare hReal 1 = 5 / 24 ∧
  (∀ i : Fin 4, pShare hReal ⟨i.val + 2, by omega⟩ = 7 / 48)

def claim47182 : Prop :=
  (∀ S : Finset (Fin 6), S.Nonempty →
    ∀ i ∈ S, ∀ j ∈ S, expectedWeight S i = expectedWeight S j) ∧
  (∑ S ∈ (Finset.univ : Finset (Finset (Fin 6))).filter
      (fun S => S.Nonempty), minimumWeight S) = 11 / 4 ∧
  2 < (∑ S ∈ (Finset.univ : Finset (Finset (Fin 6))).filter
      (fun S => S.Nonempty), minimumWeight S)

def claim47183 : Prop :=
  (∀ i : Fin 6, expectedSaving i = 1 / 2) ∧
  varianceValue orbitMean = 1 / 6 ∧
  maximumExpectedSaving = 1 / 2 ∧
  varianceValue orbitMean < 2 * maximumExpectedSaving

end

end MathlibPlus.Open.Research.R3290
