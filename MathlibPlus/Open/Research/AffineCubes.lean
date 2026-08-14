import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.AffineCubes

abbrev Bit := ZMod 2
abbrev BooleanVector (n : ℕ) := Fin n → Bit
abbrev Coefficients (n : ℕ) := Fin n → Fin n → Bit


def toggle (x : BooleanVector n) (j : Fin n) : BooleanVector n :=
  x + Pi.single j 1

def affineValue (a : Coefficients n) (b : Fin n → Bit)
    (i : Fin n) (x : BooleanVector n) : Bit :=
  b i + ((Finset.univ : Finset (Fin n)).erase i).sum (fun k => a i k * x k)

def edgePresent (a : Coefficients n) (b : Fin n → Bit)
    (i : Fin n) (x : BooleanVector n) : Prop :=
  x i = 0 ∧ affineValue a b i x = 1

def squareProduct (a : Coefficients n) (b : Fin n → Bit)
    (i j : Fin n) (x : BooleanVector n) : Bit :=
  affineValue a b i x * affineValue a b i (toggle x j) *
    affineValue a b j x * affineValue a b j (toggle x i)

def squareCondition (a : Coefficients n) (b : Fin n → Bit)
    (i j : Fin n) (x : BooleanVector n) : Prop :=
  x i = 0 ∧ x j = 0 → squareProduct a b i j x = 0

def subgraphC4Free (a : Coefficients n) (b : Fin n → Bit) : Prop :=
  ¬ ∃ (i j : Fin n) (x : BooleanVector n),
    i ≠ j ∧ x i = 0 ∧ x j = 0 ∧
      edgePresent a b i x ∧ edgePresent a b i (toggle x j) ∧
      edgePresent a b j x ∧ edgePresent a b j (toggle x i)

def pairSquareFree (a : Coefficients n) (b : Fin n → Bit)
    (i j : Fin n) : Prop :=
  ∀ x, squareCondition a b i j x

def crossVector (a : Coefficients n) (i j : Fin n) : Fin n → Bit :=
  fun k => if k = i ∨ k = j then 0 else a i k

def coefficientCriterion (a : Coefficients n) (b : Fin n → Bit)
    (i j : Fin n) : Prop :=
  a i j = 1 ∨ a j i = 1 ∨
    (a i j = 0 ∧ a j i = 0 ∧
      ((crossVector a i j = 0 ∧ b i = 0) ∨
        (crossVector a j i = 0 ∧ b j = 0) ∨
        (crossVector a i j = crossVector a j i ∧ b i ≠ b j)))

def omega (i : Fin n) : Finset (BooleanVector n) :=
  Finset.univ.filter (fun x => x i = 0)

def nonzeroLinearPart (a : Coefficients n) (i : Fin n) : Prop :=
  ∃ k, k ≠ i ∧ a i k ≠ 0

def directionFull (a : Coefficients n) (b : Fin n → Bit) (i : Fin n) : Prop :=
  ∀ x, x i = 0 → affineValue a b i x = 1

def directionZero (a : Coefficients n) (b : Fin n → Bit) (i : Fin n) : Prop :=
  ∀ x, x i = 0 → affineValue a b i x = 0

def directionDensity (a : Coefficients n) (b : Fin n → Bit) (i : Fin n) : ℝ :=
  (Fintype.card {x : BooleanVector n // x i = 0 ∧ affineValue a b i x = 1} : ℝ) /
    (Fintype.card {x : BooleanVector n // x i = 0} : ℝ)

def fullCount (a : Coefficients n) (b : Fin n → Bit) : ℕ := by
  classical
  exact (Finset.univ.filter (directionFull a b)).card

def nonconstantCount (a : Coefficients n) : ℕ := by
  classical
  exact (Finset.univ.filter (nonzeroLinearPart a)).card

def zeroCount (a : Coefficients n) (b : Fin n → Bit) : ℕ := by
  classical
  exact (Finset.univ.filter (directionZero a b)).card

def edgeCount (a : Coefficients n) (b : Fin n → Bit) : ℕ :=
  ∑ i : Fin n, Fintype.card {x : BooleanVector n // x i = 0 ∧ affineValue a b i x = 1}

def edgeBound (n : ℕ) : ℝ := (n + 1) * (2 : ℝ) ^ n / 4

def specialCoefficients (n : ℕ) : Coefficients n :=
  fun i k => if i.val = 0 then 0 else if k = i then 0 else 1

def specialConstants (n : ℕ) : Fin n → Bit :=
  fun i => if i.val = 0 then 1 else 0

def claim46109 : Prop :=
  ∀ n : ℕ, ∀ a : Coefficients n, ∀ b : Fin n → Bit,
    subgraphC4Free a b ↔
      ∀ i j : Fin n, i ≠ j → ∀ x, squareCondition a b i j x

def claim46110 : Prop :=
  ∀ n : ℕ, ∀ a : Coefficients n, ∀ b : Fin n → Bit,
    ∀ i j : Fin n, i ≠ j →
      pairSquareFree a b i j ↔ coefficientCriterion a b i j

def claim46111 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a : Coefficients n, ∀ b : Fin n → Bit,
    (∀ i j : Fin n, i ≠ j → pairSquareFree a b i j) →
      (∀ i, nonzeroLinearPart a i → directionDensity a b i = 1 / 2) ∧
      (∀ i, ¬ nonzeroLinearPart a i →
        directionFull a b i ∨ directionZero a b i) ∧
      fullCount a b ≤ 1 ∧
      n = fullCount a b + nonconstantCount a + zeroCount a b ∧
      (∑ i : Fin n, directionDensity a b i : ℝ) =
        (fullCount a b : ℝ) + (nonconstantCount a : ℝ) / 2

def claim46112 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a : Coefficients n, ∀ b : Fin n → Bit,
    subgraphC4Free a b →
      (edgeCount a b : ℝ) ≤ edgeBound n ∧
      ((edgeCount a b : ℝ) = edgeBound n ↔
        ∃ i : Fin n, directionFull a b i ∧
          ∀ j : Fin n, j ≠ i → nonzeroLinearPart a j)

def claim46113 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    subgraphC4Free (specialCoefficients n) (specialConstants n) ∧
      (edgeCount (specialCoefficients n) (specialConstants n) : ℝ) = edgeBound n

end MathlibPlus.Open.Research.AffineCubes
