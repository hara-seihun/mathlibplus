import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators

/-- The finite Toeplitz minors used for the order-three Pólya-frequency condition. -/
def toeplitzEntry (f : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i ≤ j then f (j - i) else 0

def PF3Sequence (f : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ), m ≤ 3 →
    ∀ (r c : Fin m → ℕ), StrictMono r → StrictMono c →
      0 ≤ Matrix.det (fun i j => toeplitzEntry f (r i) (c j))

def PFInfinitySequence (f : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ),
    ∀ (r c : Fin m → ℕ), StrictMono r → StrictMono c →
      0 ≤ Matrix.det (fun i j => toeplitzEntry f (r i) (c j))

def EntirePowerSeries (f : ℕ → ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → Summable (fun n => ‖f n‖ * R ^ n)

def NonpolynomialSequence (f : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, ∃ n : ℕ, d < n ∧ f n ≠ 0

/-- Claim 13076. -/
def PF3StrictRatios : Prop :=
  ∀ (f : ℕ → ℝ),
    (∀ n, 0 < f n) →
    EntirePowerSeries f →
    NonpolynomialSequence f →
    PF3Sequence f →
    ∀ n, 1 ≤ n →
      f n / f (n - 1) > f (n + 1) / f n ∧
        f n ^ 2 > f (n - 1) * f (n + 1)

def polynomialP (t : ℝ) (z : ℂ) : ℂ :=
  (1 + 2 * (t : ℂ) * z + 2 * (t : ℂ) ^ 2 * z ^ 2) *
    (1 + (t : ℂ) ^ 3 * z / 8)

def polynomialCoeff (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1
  else if n = 1 then 2 * t + t ^ 3 / 8
  else if n = 2 then 2 * t ^ 2 + t ^ 4 / 4
  else if n = 3 then t ^ 5 / 4
  else 0

/-- Claim 13079. -/
def BoundaryPolynomialPF3 : Prop :=
  ∀ t : ℝ, 0 < t →
    (∀ z : ℂ,
      polynomialP t z = 0 ↔
        z = (-1 + Complex.I) / (2 * (t : ℂ)) ∨
        z = (-1 - Complex.I) / (2 * (t : ℂ)) ∨
        z = (-8 : ℂ) / (t : ℂ) ^ 3) ∧
    Complex.arg ((-1 + Complex.I) / (2 * (t : ℂ))) = 3 * Real.pi / 4 ∧
    Complex.arg ((-1 - Complex.I) / (2 * (t : ℂ))) = -(3 * Real.pi / 4) ∧
    Complex.arg ((-8 : ℂ) / (t : ℂ) ^ 3) = Real.pi ∧
    PF3Sequence (polynomialCoeff t)

def exponentialPolynomialCoeff (t ε : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (min n 3 + 1),
    polynomialCoeff t k * ε ^ (n - k) / (Nat.factorial (n - k) : ℝ)

def exponentialPolynomial (t ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((ε : ℂ) * z) * polynomialP t z

/-- Claim 13080. -/
def ExponentialStrictificationPF3 : Prop :=
  ∀ t ε : ℝ, 0 < t → 0 < ε →
    let f := exponentialPolynomialCoeff t ε
    let F : ℂ → ℂ := fun z => ∑' n : ℕ, (f n : ℂ) * z ^ n
    F 0 = 1 ∧
      (∀ n, 0 < f n) ∧
      EntirePowerSeries f ∧
      NonpolynomialSequence f ∧
      (∀ z, F z = exponentialPolynomial t ε z) ∧
      PFInfinitySequence (fun n => ε ^ n / (Nat.factorial n : ℝ)) ∧
      PF3Sequence f

def newtonQ (A B C : ℝ) (n : ℕ) : ℝ :=
  1 + A * (n : ℝ) + B * (n : ℝ) * ((n - 1 : ℕ) : ℝ) +
    C * (n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)

def factorialRescaledCoeff (t ε : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * exponentialPolynomialCoeff t ε n

/-- Claim 13082. -/
def NewtonFallingFactorialCoefficientFormula : Prop :=
  ∀ t ε : ℝ, 0 < t → 0 < ε →
    ∀ n : ℕ,
      factorialRescaledCoeff t ε n =
        ε ^ n *
          newtonQ
            (polynomialCoeff t 1 / ε)
            (polynomialCoeff t 2 / ε ^ 2)
            (polynomialCoeff t 3 / ε ^ 3)
            n

def fallingFactorial (x k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, ((x - i : ℕ) : ℝ)

/-- Claim 13083. -/
def NewtonUltraTuranIdentity : Prop :=
  (∀ (A B C : ℝ) (n : ℕ), 1 ≤ n →
    let x := n - 1
    newtonQ A B C n ^ 2 - newtonQ A B C (n - 1) * newtonQ A B C (n + 1) =
      A ^ 2 - 2 * B +
        2 * (A * B - 3 * A * C + 2 * B ^ 2 - 3 * C) * fallingFactorial x 1 +
        2 * (B + 3 * C) ^ 2 * fallingFactorial x 2 +
        2 * C * (2 * B + 9 * C) * fallingFactorial x 3 +
        3 * C ^ 2 * fallingFactorial x 4) ∧
  (∀ t : ℝ, 0 < t →
    let p₁ := polynomialCoeff t 1
    let p₂ := polynomialCoeff t 2
    let p₃ := polynomialCoeff t 3
    p₁ ^ 2 - 2 * p₂ = t ^ 6 / 64 ∧
      p₁ * p₂ - 3 * p₃ = t ^ 3 * (t ^ 4 + 128) / 32 ∧
      2 * p₂ ^ 2 - 3 * p₁ * p₃ =
        t ^ 4 * (t ^ 2 - 4 * t + 16) * (t ^ 2 + 4 * t + 16) / 32 ∧
      0 < p₁ ^ 2 - 2 * p₂ ∧
      0 < p₁ * p₂ - 3 * p₃ ∧
      0 < 2 * p₂ ^ 2 - 3 * p₁ * p₃) ∧
  (∀ t ε : ℝ, 0 < t → 0 < ε →
    ∀ n : ℕ, 1 ≤ n →
      exponentialPolynomialCoeff t ε n ^ 2 >
        (((n + 1 : ℕ) : ℝ) / (n : ℝ)) *
          exponentialPolynomialCoeff t ε (n - 1) *
          exponentialPolynomialCoeff t ε (n + 1))

end

end MathlibPlus.Open.ResearchFormalization
