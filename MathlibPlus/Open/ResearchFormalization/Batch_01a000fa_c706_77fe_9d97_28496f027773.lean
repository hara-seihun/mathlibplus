import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev Vector3 := Fin 3 → ℝ

def determinant3 (c₁ c₂ c₃ : Vector3) : ℝ :=
  Matrix.det (fun i j => (![c₁, c₂, c₃] j) i)

def fiveColumnRatio (c₁ c₂ c₃ c₄ c₅ : Vector3) : ℝ :=
  determinant3 c₁ c₂ c₃ * determinant3 c₁ c₄ c₅ /
    (determinant3 c₁ c₂ c₄ * determinant3 c₁ c₃ c₅)

def quadraticRemainderAtZero (c₂ : ℝ → Vector3) (p d : Vector3) : Prop :=
  ∃ C δ : ℝ,
    0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ‖c₂ ε - p - ε • d‖ ≤ C * ε ^ 2

def dividedDifferenceFlagCoordinate
    (p d c₃ c₄ c₅ : Vector3) : ℝ :=
  determinant3 p d c₃ * determinant3 p c₄ c₅ /
    (determinant3 p d c₄ * determinant3 p c₃ c₅)

/-- Claim 44547, including its moment-curve specialization. -/
def claim44547 : Prop :=
  (∀ (p d c₃ c₄ c₅ : Vector3) (c₂ : ℝ → Vector3),
      quadraticRemainderAtZero c₂ p d →
      (∀ ε : ℝ, 0 < ε →
        determinant3 p (c₂ ε) c₄ ≠ 0 ∧
          determinant3 p c₃ c₅ ≠ 0) →
      determinant3 p d c₄ ≠ 0 →
      determinant3 p c₃ c₅ ≠ 0 →
      Filter.Tendsto
        (fun ε : ℝ => fiveColumnRatio p (c₂ ε) c₃ c₄ c₅)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (dividedDifferenceFlagCoordinate p d c₃ c₄ c₅))) ∧
    (let v : ℝ → Vector3 := fun s => ![1, s, s ^ 2]
     let I : ℝ → ℝ := fun ε =>
       fiveColumnRatio (v 0) (v ε) (v 1) (v 2) (v 3)
     let v₀' : Vector3 := ![0, 1, 0]
     (∀ ε : ℝ, 0 < ε → ε < 1 →
        I ε = (1 - ε) / (2 * (2 - ε))) ∧
       Filter.Tendsto I (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (1 / 4 : ℝ)) ∧
       dividedDifferenceFlagCoordinate (v 0) v₀' (v 1) (v 2) (v 3) =
         (1 / 4 : ℝ))

/-- Claim 44614, with the named cell and probe ordinate as parameters. -/
def claim44614
    (X : ℝ) (t₀ y₀ lambda : ℝ) (N : ℕ)
    (firstCutoffCell : Set ℝ) (probeOrdinate : ℝ) : Prop :=
  X = 6000000185827 ∧
    t₀ = 99 / 10000 ∧
    y₀ = 1 / 100 ∧
    lambda = t₀ + y₀ ^ 2 / 2 ∧
    lambda = 199 / 20000 ∧
    lambda < 1 / 100 ∧
    N = 690988 ∧
    firstCutoffCell = Set.Ico
      (4 * Real.pi * ((N : ℝ) ^ 2 - t₀ / 16))
      (4 * Real.pi * (((N + 1 : ℕ) : ℝ) ^ 2 - t₀ / 16)) ∧
    probeOrdinate = y₀

def polyDerivativeIter : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, p => p
  | n + 1, p => polyDerivativeIter n p.derivative
  termination_by n => n

def productPolynomial {n : ℕ} (α : Fin n → ℝ) : Polynomial ℝ :=
  ∏ ν : Fin n, (1 + Polynomial.C (α ν) * Polynomial.X)

def powerSum {n : ℕ} (α : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ ν : Fin n, (α ν) ^ k

def derivativeDeterminant {n : ℕ} (α : Fin n → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 4 =>
    (polyDerivativeIter (3 + (j : ℕ) - (i : ℕ)) (productPolynomial α)).eval 0)

def fourthDeterminantPolynomial {n : ℕ} (α : Fin n → ℝ) : ℝ :=
  let q₂ := powerSum α 2
  let q₃ := powerSum α 3
  let q₄ := powerSum α 4
  let q₅ := powerSum α 5
  let q₆ := powerSum α 6
  q₂ ^ 6 - 12 * q₂ ^ 4 * q₄ + 8 * q₂ ^ 3 * q₃ ^ 2 +
      20 * q₂ ^ 3 * q₆ - 48 * q₂ ^ 2 * q₃ * q₅ +
      21 * q₂ ^ 2 * q₄ ^ 2 + 24 * q₂ * q₃ ^ 2 * q₄ -
      60 * q₂ * q₄ * q₆ + 48 * q₂ * q₅ ^ 2 - 12 * q₃ ^ 4 +
      40 * q₃ ^ 2 * q₆ - 48 * q₃ * q₄ * q₅ + 18 * q₄ ^ 3

/-- Claim 44658.  The displayed signs restore the separating minus signs
that are implicit in the packet's line-broken polynomial expression. -/
def claim44658 : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℝ),
    derivativeDeterminant α = 12 * fourthDeterminantPolynomial α

end MathlibPlus.Open.ResearchFormalizationBatch
