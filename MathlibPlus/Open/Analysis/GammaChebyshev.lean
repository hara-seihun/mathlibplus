import Mathlib

noncomputable section

namespace MathlibPlus.Open

/-- The Gamma(5/2,1) density, written explicitly so its expectation is unambiguous. -/
def gammaFiveHalvesOneDensity (z : ℝ) : ℝ :=
  (4 / (3 * Real.sqrt Real.pi)) * Real.rpow z ((3 : ℝ) / 2) * Real.exp (-z)

/-- Expectation under the Gamma(5/2,1) law. -/
def gammaFiveHalvesOneExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ),
    f z * gammaFiveHalvesOneDensity z ∂MeasureTheory.volume

/-- P_j(y) = E[(y+Z)^(2j)] for Z ~ Gamma(5/2,1). -/
def gammaFiveHalvesOneP (j : Fin 5) (y : ℝ) : ℝ :=
  gammaFiveHalvesOneExpectation (fun z => (y + z) ^ (2 * (j : ℕ)))

/-- The two tuples appearing in the first-cell sign change. -/
def gammaFirstTuple (i : Fin 5) : ℝ :=
  (((i : ℕ) : ℝ) + 1) / 20

def gammaSecondTuple (i : Fin 5) : ℝ :=
  (((i : ℕ) : ℝ) + 6) / 20

/-- Strictly increasing tuples in the first logarithmic cell. -/
def inFirstLogarithmicCell (x : Fin 5 → ℝ) : Prop :=
  (∀ i : Fin 5, 0 < x i ∧ x i < Real.log 2) ∧
    (∀ ⦃i j : Fin 5⦄, i < j → x i < x j)

/-- Determinantal criterion for a strict Chebyshev system on this cell. -/
def strictChebyshevOnFirstLogarithmicCell
    (P : Fin 5 → ℝ → ℝ) : Prop :=
  ∀ x : Fin 5 → ℝ,
    inFirstLogarithmicCell x →
    Matrix.det (fun i j => P j (x i)) ≠ 0

/-- The admitted Gamma sign-change counterexample and its Chebyshev consequence. -/
def gammaFiveHalvesFirstCellSignChange : Prop :=
  let P : Fin 5 → ℝ → ℝ := gammaFiveHalvesOneP
  (Matrix.det (fun i j => P j (gammaFirstTuple i)) =
      -(12499876633097367 : ℝ) / 1024000000000000000000) ∧
    (Matrix.det (fun i j => P j (gammaSecondTuple i)) =
      (283221976330376829 : ℝ) / 2048000000000000000000) ∧
    (-(12499876633097367 : ℝ) / 1024000000000000000000 < 0) ∧
    ((283221976330376829 : ℝ) / 2048000000000000000000 > 0) ∧
    inFirstLogarithmicCell gammaFirstTuple ∧
    inFirstLogarithmicCell gammaSecondTuple ∧
    (∃ x : Fin 5 → ℝ,
      inFirstLogarithmicCell x ∧
        Matrix.det (fun i j => P j (x i)) = 0) ∧
    ¬ strictChebyshevOnFirstLogarithmicCell P

end MathlibPlus.Open
