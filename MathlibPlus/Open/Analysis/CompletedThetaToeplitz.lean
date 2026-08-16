import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators
open MeasureTheory

noncomputable def completedThetaShell (n : ℕ) (u : ℝ) : ℝ :=
  let x_n : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)
  2 * Real.exp (u / 2) * x_n * (2 * x_n - 3) * Real.exp (-x_n)

noncomputable def completedThetaSource (u : ℝ) : ℝ :=
  ∑' k : ℕ, completedThetaShell (k + 1) |u|

noncomputable def completedThetaAutocorrelation (y : ℝ) : ℝ :=
  ∫ d : ℝ, completedThetaSource (y + d) * completedThetaSource (y - d)

noncomputable def completedThetaSecondMoment (y : ℝ) : ℝ :=
  ∫ d : ℝ, d ^ 2 * completedThetaSource (y + d) * completedThetaSource (y - d)

noncomputable def completedThetaQuotient (y : ℝ) : ℝ :=
  completedThetaSecondMoment y / completedThetaAutocorrelation y

noncomputable def completedThetaSamplePoint (j : Fin 9) : ℝ :=
  2 * (j.1 : ℝ) / 25

noncomputable def completedThetaToeplitzMatrix : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => completedThetaQuotient
    |completedThetaSamplePoint i - completedThetaSamplePoint j|

def completedThetaWitness : Fin 9 → ℝ :=
  ![(-31335 : ℝ), 178814, -488808, 841294, -1000000, 841294, -488808, 178814, -31335]

def finiteQuadraticForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, q i * M i j * q j

noncomputable def finiteRayleighQuotient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) : ℝ :=
  finiteQuadraticForm M q / ∑ i : Fin n, q i ^ 2

noncomputable def completedThetaQuadraticCenter : ℝ :=
  -(51736507296368448 : ℝ) / (10 : ℝ) ^ 13

noncomputable def completedThetaQuadraticRadiusBound : ℝ :=
  (77 : ℝ) / (10 : ℝ) ^ 15

noncomputable def completedThetaRayleighPrefix : ℝ :=
  -(17482504775937771 : ℝ) / (10 : ℝ) ^ 25

/-- Claim 11939: the displayed finite Toeplitz witness and its certified numerical data. -/
noncomputable def completedThetaExplicitNegativeToeplitzWitness : Prop :=
  let M := completedThetaToeplitzMatrix
  let q := completedThetaWitness
  let Q := finiteQuadraticForm M q
  let R := finiteRayleighQuotient M q
  Q < 0 ∧
    |Q - completedThetaQuadraticCenter| < completedThetaQuadraticRadiusBound ∧
    completedThetaRayleighPrefix - (1 : ℝ) / (10 : ℝ) ^ 25 < R ∧
    R ≤ completedThetaRayleighPrefix

noncomputable def completedThetaFourShellSource (u : ℝ) : ℝ :=
  ∑ k : Fin 4, completedThetaShell (k.1 + 1) |u|

noncomputable def completedThetaTailBound : ℝ :=
  4 * Real.pi ^ 2 * (5 : ℝ) ^ 4 * Real.exp (-25 * Real.pi) /
    (1 - ((6 : ℝ) / 5) ^ 4 * Real.exp (-11 * Real.pi))

noncomputable def completedThetaSourceUpperBound : ℝ :=
  4 * Real.pi ^ 2 * Real.exp (-Real.pi) /
    (1 - 16 * Real.exp (-3 * Real.pi))

/-- Claim 11942: the four-shell tail, source envelope, and product-error bound. -/
def completedThetaFourShellOmissionBound : Prop :=
  ∃ ε : ℝ,
    0 ≤ ε ∧
    (∀ u : ℝ,
      |completedThetaSource u - completedThetaFourShellSource u| ≤ ε) ∧
    ε ≤ completedThetaTailBound ∧
    completedThetaTailBound < (192 : ℝ) / (10 : ℝ) ^ 32 ∧
    (∀ u : ℝ, completedThetaSource u ≤ completedThetaSourceUpperBound) ∧
    completedThetaSourceUpperBound < (1709 : ℝ) / 1000 ∧
    (∀ u v : ℝ,
      |completedThetaSource u * completedThetaSource v -
          completedThetaFourShellSource u * completedThetaFourShellSource v| ≤
        2 * completedThetaSourceUpperBound * ε + ε ^ 2)

def realAbsoluteKernelPositiveDefinite (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℝ),
    0 ≤ finiteQuadraticForm
      (fun i j => K |x i - x j|) c

/-- Claim 11940: the negative witness violates the finite-matrix criterion. -/
def completedThetaQuotientNotPositiveDefinite : Prop :=
  finiteQuadraticForm completedThetaToeplitzMatrix completedThetaWitness < 0 ∧
    ¬ realAbsoluteKernelPositiveDefinite completedThetaQuotient

end MathlibPlus.Open.Analysis
