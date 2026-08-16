import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research

abbrev BellQIndex := Fin 2 × Fin 2
abbrev BellSmallMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev BellBigMatrix := Matrix (Fin 4) (Fin 4) ℂ

/-- The Pauli matrices in the computational two-qubit tensor basis. -/
def pauliX : BellSmallMatrix := !![0, 1; 1, 0]
def pauliY : BellSmallMatrix := !![0, -Complex.I; Complex.I, 0]
def pauliZ : BellSmallMatrix := !![1, 0; 0, -1]

def kron4 (A B : BellSmallMatrix) : BellBigMatrix :=
  (Matrix.reindex (finProdFinEquiv (m := 2) (n := 2))
    (finProdFinEquiv (m := 2) (n := 2))) (Matrix.kronecker A B)

def qMatrix (x g t : ℝ) : BellBigMatrix :=
  (((2 + x) / 4 : ℝ) : ℂ) • (1 : BellBigMatrix)
    - (((1 / 2 : ℝ) : ℂ) • kron4 pauliX pauliX)
    - (((g / 4 : ℝ) : ℂ) • kron4 pauliZ pauliY)
    + (((t : ℝ) : ℂ) • kron4 pauliY pauliZ)

def bellFrame : BellBigMatrix :=
  let s : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  !![s, 0, s, 0;
     0, s, 0, s;
     0, s, 0, -s;
     s, 0, -s, 0]

def bellRepresentation (x g t : ℝ) : BellBigMatrix :=
  bellFrame.conjTranspose * qMatrix x g t * bellFrame

def bellBlockI (A : BellBigMatrix) (p : Fin 2) : ℝ :=
  (A (finProdFinEquiv (p, (0 : Fin 2)))
      (finProdFinEquiv (p, (0 : Fin 2)))).re

def bellBlockY (A : BellBigMatrix) (p : Fin 2) : ℝ :=
  (Complex.I * A (finProdFinEquiv (p, (0 : Fin 2)))
      (finProdFinEquiv (p, (1 : Fin 2)))).re

def bellCoefficientMatrix (x g t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let A := bellRepresentation x g t
  !![bellBlockI A 0, bellBlockY A 0;
     bellBlockI A 1, bellBlockY A 1]

def bellOperatorSchmidtRank (x g t : ℝ) : ℕ :=
  Matrix.rank (bellCoefficientMatrix x g t)

def tStar (x g : ℝ) : ℝ := g / (2 * (2 + x))

def rhoOf (x g : ℝ) : ℝ := g / (2 + x)

def rx (x : ℝ) : BellSmallMatrix :=
  Matrix.diagonal (fun i : Fin 2 =>
    if i = 0 then ((x / 4 : ℝ) : ℂ) else (((4 + x) / 4 : ℝ) : ℂ))

def canonicalFactor (x rho : ℝ) : BellBigMatrix :=
  kron4 (rx x) ((1 : BellSmallMatrix) - ((rho : ℝ) : ℂ) • pauliY)

def canonicalGram (x rho : ℝ) : BellBigMatrix :=
  qMatrix x ((2 + x) * rho) (rho / 2)

def pairIndex (i : Fin 4) : Fin 2 × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 2)).symm i

def pairToIndex (i : Fin 2 × Fin 2) : Fin 4 :=
  finProdFinEquiv i

/-- Partial transpose in the second factor of the original computational basis. -/
def compactPartialTranspose (A : BellBigMatrix) : BellBigMatrix :=
  fun i j =>
    let ii := pairIndex i
    let jj := pairIndex j
    A (pairToIndex (ii.1, jj.2)) (pairToIndex (jj.1, ii.2))

def quadraticForm (A : BellBigMatrix) (v : Fin 4 → ℂ) : ℂ :=
  ∑ i, star (v i) * A.mulVec v i

def positiveSemidefiniteComplex (A : BellBigMatrix) : Prop :=
  Matrix.IsHermitian A ∧ ∀ v : Fin 4 → ℂ, 0 ≤ (quadraticForm A v).re

def positiveDefiniteComplex (A : BellBigMatrix) : Prop :=
  Matrix.IsHermitian A ∧
    ∀ v : Fin 4 → ℂ, v ≠ 0 → 0 < (quadraticForm A v).re

def eigenvalue (A : BellBigMatrix) (z : ℂ) : Prop :=
  ∃ v : Fin 4 → ℂ, v ≠ 0 ∧
    A.mulVec v = fun i => z * v i

def isLeastRealEigenvalue (A : BellBigMatrix) (μ : ℝ) : Prop :=
  eigenvalue A (μ : ℂ) ∧
    ∀ ν : ℝ, eigenvalue A (ν : ℂ) → μ ≤ ν

def balancedRhoSquared (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ 2 * (72 * x * (1 - x) / (2 + x) ^ 2)

/-- The coefficient matrix, determinant, and unique rank-one gauge. -/
def claim13478 : Prop :=
  ∀ (x g t : ℝ), 0 ≤ x →
    bellCoefficientMatrix x g t =
        !![x / 4, t - g / 4;
           (4 + x) / 4, -t - g / 4] ∧
      (bellCoefficientMatrix x g t).det =
        (g - 2 * (2 + x) * t) / 4 ∧
      (bellOperatorSchmidtRank x g t = 1 ↔
        t = g / (2 * (2 + x)))

/-- Bell factorization, spectrum, and the PSD threshold. -/
def claim13479 : Prop :=
  ∀ (x g : ℝ), 0 ≤ x →
    let rho := rhoOf x g
    let R := rx x
    bellRepresentation x g (tStar x g) =
        kron4 R ((1 : BellSmallMatrix) - ((rho : ℝ) : ℂ) • pauliY) ∧
      (∀ z : ℂ,
        eigenvalue (canonicalFactor x rho) z ↔
          z = (((x * (1 + rho) / 4 : ℝ) : ℂ)) ∨
          z = (((x * (1 - rho) / 4 : ℝ) : ℂ)) ∨
          z = ((((4 + x) * (1 + rho) / 4 : ℝ) : ℂ)) ∨
          z = ((((4 + x) * (1 - rho) / 4 : ℝ) : ℂ))) ∧
      (positiveSemidefiniteComplex (canonicalFactor x rho) ↔
        |rho| ≤ 1) ∧
      (|rho| ≤ 1 ↔ |g| ≤ 2 + x)

/-- At balanced heat and x = 2/5, positivity coexists with NPT. -/
def claim13485 : Prop :=
  ∀ rho : ℝ, rho ^ 2 = balancedRhoSquared (2 / 5 : ℝ) →
    positiveDefiniteComplex (canonicalGram (2 / 5 : ℝ) rho) ∧
      isLeastRealEigenvalue
        (compactPartialTranspose (canonicalGram (2 / 5 : ℝ) rho))
        ((2 - 11 * Real.sqrt 3) / 20) ∧
      (2 - 11 * Real.sqrt 3) / 20 < 0

/-- Every nonzero heat has a small-x positive canonical output that is NPT. -/
def claim13486 : Prop :=
  ∀ lambda : ℝ, 0 < lambda →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : ℝ, 0 < x → x < ε →
        (∀ rho : ℝ,
          rho ^ 2 = 72 * lambda ^ 2 * x * (1 - x) / (2 + x) ^ 2 →
            |rho| < 1 ∧ |rho| > x / (4 + x)) ∧
        (∃ rho : ℝ,
          rho ^ 2 = 72 * lambda ^ 2 * x * (1 - x) / (2 + x) ^ 2 ∧
          positiveSemidefiniteComplex (canonicalGram x rho) ∧
          ¬ positiveSemidefiniteComplex
            (compactPartialTranspose (canonicalGram x rho)))

end MathlibPlus.Open.Research
