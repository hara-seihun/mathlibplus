import Mathlib

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Set

namespace MathlibPlus.Open.FormalizationBatch.Arithmetic

/-- The arithmetic kernel with the exact sampling range from the admitted claim. -/
def arithmeticKernel (c : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt c *
    ∑' n : ℕ,
      if 1 ≤ n ∧ (n : ℝ) < c * Real.exp (-x) then
        p ((n : ℝ) * Real.exp x / c)
      else 0

/-- An unsampled packet is zero at every sampled argument, hence its kernel vanishes. -/
def unsampledCellExactNullspace : Prop :=
  ∀ (c : ℝ) (p : ℝ → ℝ),
    1 < c →
    (∀ v : ℝ, p v ≠ 0 → |v| < 1 / c) →
    ∀ x : ℝ, 0 ≤ x → x ≤ Real.log c → arithmeticKernel c p x = 0

/-- The primitive completed-theta sum in the admitted moment formula. -/
def primitiveCompletedTheta (u : ℝ) : ℝ :=
  ∑' q : ℕ, Real.exp
    (-Real.pi * ((q + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))

/-- The admitted primitive completed-theta moment sequence. -/
def primitiveCompletedThetaMoment (n : ℕ) : ℝ :=
  2 / ((Nat.factorial (2 * n) : ℕ) : ℝ) *
    (∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2) * primitiveCompletedTheta u * u ^ (2 * n))

/-- Consecutive mixed-shift Casoratians, with the empty determinant equal to one. -/
def consecutiveMixedShiftCasoratian (m n : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin m =>
    primitiveCompletedThetaMoment (n - i.val + j.val))

/-- Square-root-order determinant positivity. -/
def squareRootOrderDeterminantPositivity : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ N₀ : ℕ, ∀ n m : ℕ,
      N₀ ≤ n → 1 ≤ m →
      (m : ℝ) ≤ A * Real.sqrt (n : ℝ) →
      0 < consecutiveMixedShiftCasoratian m n

/-- The involution on the zero divisor. -/
def zeroInvolution (lam : ℂ) : ℂ := -star lam

def fixedZeroBlock (m : ℕ) (v : ℂ) : ℝ :=
  (m : ℝ) * Complex.normSq v

def pairedZeroGram (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    (m : ℝ) *
      if i.val = 0 ∧ j.val = 1 then 1
      else if i.val = 1 ∧ j.val = 0 then 1
      else 0

def positivePairedVector : Fin 2 → ℝ := fun _ => 1

def negativePairedVector : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 1 else -1

/-- A concrete signature-(1,1) encoding for the displayed paired block. -/
def pairedGramHasSignatureOneOne (m : ℕ) : Prop :=
  0 < m ∧
    Matrix.mulVec (pairedZeroGram m) positivePairedVector =
      (m : ℝ) • positivePairedVector ∧
    Matrix.mulVec (pairedZeroGram m) negativePairedVector =
      (- (m : ℝ)) • negativePairedVector

def primeZeroBlock (p : ℕ) (lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i : Fin 2 =>
    if i.val = 0 then
      Complex.exp (Complex.ofReal (Real.log (p : ℝ)) * lam)
    else
      Complex.exp (Complex.ofReal (Real.log (p : ℝ)) * (-star lam)))

/-- Exact fixed, paired, and prime block signatures. -/
def exactSignatureOfZeroBlocks : Prop :=
  (∀ (lam : ℂ), zeroInvolution lam = lam ↔ lam.re = 0) ∧
  (∀ (m : ℕ) (lam v : ℂ), 0 < m → zeroInvolution lam = lam → v ≠ 0 →
    0 < fixedZeroBlock m v) ∧
  (∀ (m : ℕ) (lam : ℂ), 0 < m → zeroInvolution lam ≠ lam →
    pairedGramHasSignatureOneOne m) ∧
  (∀ (p : ℕ) (lam : ℂ), Nat.Prime p →
    Matrix.IsDiag (primeZeroBlock p lam) ∧
    primeZeroBlock p lam = Matrix.diagonal (fun i : Fin 2 =>
      if i.val = 0 then
        Complex.exp (Complex.ofReal (Real.log (p : ℝ)) * lam)
      else
        Complex.exp (Complex.ofReal (Real.log (p : ℝ)) * (-star lam))))

def coefficientIdentity : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

def coefficientX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 1 ∧ j.val = 0 then 1
    else 0

def coefficientZ : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i.val = j.val then if i.val = 0 then 1 else -1 else 0

def coefficientPMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  ((2 : ℂ)⁻¹) • (coefficientIdentity - coefficientZ)

def normalizedKlingenCoefficientMatrix (κ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  coefficientX + κ • coefficientPMinus

/-- The Hecke-odd symmetric part of the normalized Klingen matrix. -/
def heckeOddSymmetricPartIsX : Prop :=
  ∀ κ : ℂ,
    ((2 : ℂ)⁻¹) •
        (normalizedKlingenCoefficientMatrix κ -
          coefficientZ * normalizedKlingenCoefficientMatrix κ * coefficientZ) = coefficientX

end MathlibPlus.Open.FormalizationBatch.Arithmetic
