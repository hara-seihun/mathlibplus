import Mathlib

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchSplitAndWedge

def splitWitness : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then 1
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then -1
    else 0

def entrywiseConjugate (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => star (X i j)

def splitForm (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (1 / 2 : ℝ) * Complex.re (Matrix.trace (X * entrywiseConjugate X))

def compactNorm (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (1 / 2 : ℝ) * Complex.re (Matrix.trace (X * Matrix.conjTranspose X))

def claim12136 : Prop :=
  splitForm splitWitness = -1 ∧ compactNorm splitWitness = 1 ∧
    splitForm splitWitness ≠ compactNorm splitWitness

def wedge (u v : Fin 2 → ℂ) : ℂ :=
  u 0 * v 1 - u 1 * v 0

def reflection (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => if i = (0 : Fin 2) then star (v 0) else -star (v 1)

def veronese (α : ℂ) : Fin 2 → ℂ :=
  fun i => if i = (0 : Fin 2) then 1 else α

def directEnergy (u v : Fin 2 → ℂ) : ℝ := Complex.normSq (wedge u v)

def reflectedEnergy (u v : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (wedge u (reflection v))

def claim12138 : Prop :=
  ∀ α β : ℂ,
    directEnergy (veronese α) (veronese β) = Complex.normSq (α - β) ∧
      reflectedEnergy (veronese α) (veronese β) =
        Complex.normSq (α + star β)

def commutesWithReflection (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ v : Fin 2 → ℂ, Matrix.mulVec A (reflection v) = reflection (Matrix.mulVec A v)

def claim12147 : Prop :=
  ∀ (A : Matrix (Fin 2) (Fin 2) ℂ),
    Matrix.det A ≠ 0 → commutesWithReflection A →
    (0 < Complex.normSq (Matrix.det A)) ∧
      ∀ α β : ℂ,
        directEnergy (Matrix.mulVec A (veronese α))
            (Matrix.mulVec A (veronese β)) =
            Complex.normSq (Matrix.det A) *
              directEnergy (veronese α) (veronese β) ∧
        reflectedEnergy (Matrix.mulVec A (veronese α))
            (Matrix.mulVec A (veronese β)) =
            Complex.normSq (Matrix.det A) *
              reflectedEnergy (veronese α) (veronese β) ∧
        (2 * reflectedEnergy (Matrix.mulVec A (veronese α))
              (Matrix.mulVec A (veronese β)) -
            directEnergy (Matrix.mulVec A (veronese α))
              (Matrix.mulVec A (veronese β))) =
          Complex.normSq (Matrix.det A) *
            (2 * reflectedEnergy (veronese α) (veronese β) -
              directEnergy (veronese α) (veronese β)) ∧
        ((2 * reflectedEnergy (Matrix.mulVec A (veronese α))
              (Matrix.mulVec A (veronese β)) -
            directEnergy (Matrix.mulVec A (veronese α))
              (Matrix.mulVec A (veronese β))) < 0 ↔
          (2 * reflectedEnergy (veronese α) (veronese β) -
            directEnergy (veronese α) (veronese β) < 0))

end MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchSplitAndWedge
