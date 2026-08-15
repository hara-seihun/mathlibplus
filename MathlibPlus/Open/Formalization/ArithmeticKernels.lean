import Mathlib

namespace MathlibPlus.Open.Formalization.ArithmeticKernels

noncomputable section

open scoped BigOperators
open Filter

/-- Claim 59439: the three exact rational margins remain positive under the stated error. -/
def claim59439 : Prop :=
  let m_f : ℝ := 0.0013129967192460183142
  let m_b : ℝ := 0.000058093232689233683405437434725615050248801708221435546875
  let m_t : ℝ := 0.009385823867106693485628209921570239
  m_b < m_f ∧ m_b < m_t ∧
    ∀ delta : ℝ, |delta| ≤ 1 / 100000 →
      0 < m_f - |delta| ∧ 0 < m_b - |delta| ∧ 0 < m_t - |delta|

def kernel59472 (x t : ℝ) : ℝ :=
  Real.exp (-5 * t / 4 - x * Real.exp (-t)) +
    Real.exp (5 * t / 4 - x * Real.exp t)

def weight59472 (n : ℕ) (t : ℝ) : ℝ :=
  kernel59472 (Real.pi * (n : ℝ) ^ 2) t

/-- Claim 59472: strict total positivity of the order-two kernel. -/
def claim59472 : Prop :=
  (∀ x t : ℝ, 7 / 4 ≤ x → 0 < t → 0 < kernel59472 x t) ∧
    (∀ x₁ x₂ t₁ t₂ : ℝ,
      7 / 4 ≤ x₁ → x₁ < x₂ → 0 < t₁ → t₁ < t₂ →
        0 < kernel59472 x₁ t₁ * kernel59472 x₂ t₂ -
          kernel59472 x₁ t₂ * kernel59472 x₂ t₁) ∧
    (∀ n₁ n₂ : ℕ, 0 < n₁ → n₁ < n₂ →
      ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
        0 < weight59472 n₁ t₁ * weight59472 n₂ t₂ -
          weight59472 n₁ t₂ * weight59472 n₂ t₁)

def sign59474 (n : ℕ) : ℝ := (-1 : ℝ) ^ n
def error59474 (n : ℕ) : ℝ := Real.exp (-(3 : ℝ) * (n : ℝ) / 2)
def root59474 (n : ℕ) : ℝ := 1 / 2 + sign59474 n * error59474 n
def polynomial59474 (n : ℕ) (x : ℝ) : ℝ :=
  sign59474 n * (x - root59474 n)

/-- Claim 59474: alternating terminal roots do not force a positive center value. -/
def claim59474 : Prop :=
  ∀ n : ℕ,
    (∀ x : ℝ, polynomial59474 n x = 0 ↔ x = root59474 n) ∧
      |root59474 n - 1 / 2| = error59474 n ∧
      (root59474 n - 1 / 2) * (root59474 (n + 1) - 1 / 2) < 0 ∧
      polynomial59474 n (1 / 2) = -error59474 n

def primeTerm59511 (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ,
    if 1 ≤ k then
      ((Real.log (p : ℝ) /
          Real.rpow (p : ℝ) ((k : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp
          (-Complex.I * (k : ℂ) * (t : ℂ) * (Real.log (p : ℝ) : ℂ))
    else 0

def primeSum59511 (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, primeTerm59511 p t

def primeMain59511 (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1)

def primeDerivative59511 (P : Finset ℕ) : ℝ :=
  2 * Real.pi * ∑ p ∈ P,
    Real.sqrt (p : ℝ) * Real.log (p : ℝ) /
      (Real.sqrt (p : ℝ) - 1) ^ 2

def coherentPrimeFrequency59511 (P : Finset ℕ) (N q : ℕ) : Prop :=
  1 ≤ q ∧ q ≤ N ^ P.card ∧
    ‖primeSum59511 P (q : ℝ) - (primeMain59511 P : ℂ)‖ ≤
      primeDerivative59511 P / (N : ℝ) ∧
    ‖primeSum59511 P (q : ℝ)‖ ≥
      primeMain59511 P - primeDerivative59511 P / (N : ℝ)

/-- Claim 59511: simultaneous rational approximation at an integer frequency. -/
def claim59511 : Prop :=
  ∀ P : Finset ℕ,
    P.Nonempty → (∀ p ∈ P, Nat.Prime p) →
      (∀ N : ℕ, 1 ≤ N → ∃ q : ℕ,
        coherentPrimeFrequency59511 P N q) ∧
      (∀ N : ℕ,
        1 ≤ N →
          2 * primeDerivative59511 P / primeMain59511 P ≤ (N : ℝ) →
            ∃ q : ℕ,
              1 ≤ q ∧ q ≤ N ^ P.card ∧
                ‖primeSum59511 P (q : ℝ)‖ ≥ primeMain59511 P / 2)

/-- Claim 59654: approximate reflection bounds force a critical-line band. -/
def claim59654 : Prop :=
  ∀ (H Hᵣ : ℂ) (r c epsilon eta : ℝ) (a : ℝ → ℂ),
    c > 0 →
      c * |2 * r - 1| ≤ ‖a (2 * r - 1)‖ →
      H = a (2 * r - 1) →
      ‖Hᵣ + H‖ ≤ epsilon →
      ‖Hᵣ - H‖ ≤ eta →
      |2 * r - 1| ≤ (epsilon + eta) / (2 * c)

/-- Claim 59704: the simultaneous endpoint-index construction. -/
def claim59704 : Prop :=
  ∀ (P : ℝ → ℝ) (g : ℕ → ℕ) (F : ℂ → ℂ),
    P 0 ≠ 0 →
      (∃ z : ℂ, F z = 0 ∧ z.im ≠ 0) →
        ∃ (H : ℕ → ℝ → ℝ) (k t : ℕ → ℕ),
          (∀ N : ℕ, Continuous (H N)) ∧
          (∀ (N : ℕ) (y : ℝ),
            0 ≤ H N (P (-y) / P 0) ∧
              H N (P (-y) / P 0) = (k N : ℝ)) ∧
          (∀ N : ℕ, k N = t N ∧ k N = g N) ∧
          (∃ z : ℂ, F z = 0 ∧ z.im ≠ 0)

def exponentialMoment59711 (lambda theta : ℕ → ℝ) (kappa delta : ℝ) : Prop :=
  Summable (fun n =>
    |Real.sinh (kappa * lambda n * theta n)| * Real.exp (delta * lambda n))

def polynomialLocks59711 (lambda theta : ℕ → ℝ) (kappa : ℝ) : Prop :=
  ∀ q : ℕ,
    ∑' n : ℕ,
      Real.sinh (kappa * lambda n * theta n) * lambda n ^ q = 0

/-- Claim 59711: exponential moments and all polynomial locks kill every imbalance. -/
def claim59711 : Prop :=
  ∀ (lambda theta : ℕ → ℝ) (kappa : ℝ),
    (∀ n : ℕ, 0 < lambda n ∧ lambda n < lambda (n + 1)) →
      kappa ≠ 0 →
        (∀ delta : ℝ,
          delta > 0 → exponentialMoment59711 lambda theta kappa delta →
            polynomialLocks59711 lambda theta kappa →
              ∀ n : ℕ, theta n = 0) ∧
        (polynomialLocks59711 lambda theta kappa →
          ((∃ n : ℕ, theta n ≠ 0) →
            ∀ delta : ℝ, delta > 0 →
              ¬ exponentialMoment59711 lambda theta kappa delta))

def kernel59712 (x u : ℝ) : ℝ :=
  x * (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
    Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))

/-- Claim 59712: the fixed ordered columns have a negative rank-two determinant. -/
def claim59712 : Prop :=
  let u₁ : ℝ := -2 * Real.log 4
  let u₂ : ℝ := 0
  u₁ < u₂ ∧
    ∀ x₁ x₂ : ℝ,
      1 / 2 ≤ x₁ → x₁ < 1 → 1 ≤ x₂ → x₂ < 2 →
        kernel59712 x₁ u₁ * kernel59712 x₂ u₂ -
            kernel59712 x₁ u₂ * kernel59712 x₂ u₁ < 0

/-- Claim 59842: endpoint inequalities detect surjectivity. -/
def claim59842 : Prop :=
  ∀ (P : ℝ → ℝ), P 0 ≠ 0 →
    (Function.Surjective P ↔
      ∀ (H : ℕ → ℝ → ℝ),
        (∀ (N : ℕ) (y : ℝ), 0 ≤ H N (P (-y) / P 0)) →
          ∀ (N : ℕ) (q : ℝ), 0 ≤ H N q)

/-- Claim 59892: the shell shift defeats every fixed polynomial factor. -/
def claim59892 : Prop :=
  ∀ (C : ℝ), C > 0 →
    ∀ k : ℕ, ∃ N m : ℕ,
      0 < N ∧ 0 < m ∧ N = m ∧
        (m : ℝ) ^ 2 ≥
          (3 / (2 * Real.pi)) * (N : ℝ) + (k : ℝ) * Real.sqrt (N : ℝ) ∧
        Real.exp (3 * (N : ℝ) / 2 - Real.pi * ((m : ℝ) - 1) ^ 2) >
          C * (N : ℝ) ^ k *
            Real.exp (3 * (N : ℝ) / 2 - Real.pi * (m : ℝ) ^ 2)

/-- Claim 59893: divisibility by every increasing power forces both differences away. -/
def claim59893 : Prop :=
  ∀ (R : Type*) [Semiring R] [NoZeroDivisors R]
    (Q A P L : Polynomial R),
    Q ≠ 0 →
      (∀ r : ℕ, Polynomial.X ^ (r + 1) * Q ∣ A) →
        Q * P + L * A = 0 → A = 0 ∧ P = 0

/-- Claim 59953: one-sided derivative data do not determine a global function. -/
def claim59953 : Prop :=
  ∀ (a : ℝ) (S : Set ℝ),
    S ⊆ Set.Ici a →
      ∃ f g : ℝ → ℝ,
        f ≠ g ∧ Differentiable ℝ f ∧ Differentiable ℝ g ∧
          f a = g a ∧ ∀ x : ℝ, x ∈ S → deriv f x = deriv g x

def primeFrequency59970 (p : ℕ → ℕ) : ℕ → ℝ :=
  fun n => Real.log (p n : ℝ)

def primeAmplitude59970 (p : ℕ → ℕ) (theta : ℕ → ℝ) : ℕ → ℝ :=
  fun n => primeFrequency59970 p n * theta n

/-- Claim 59970: unbounded positive levels of one logarithmic moment force balance. -/
def claim59970 : Prop :=
  ∀ (p : ℕ → ℕ) (theta : ℕ → ℝ),
    (∀ n : ℕ, Nat.Prime (p n)) →
      (∀ i j : ℕ, i ≠ j → p i ≠ p j) →
        Summable (fun n =>
          |primeAmplitude59970 p theta n| * primeFrequency59970 p n) →
          ∀ (levels : ℕ → ℝ),
            (∀ l : ℕ, 0 < levels l) →
            Tendsto levels atTop atTop →
            (∀ l : ℕ,
              ∑' n : ℕ,
                Real.sinh (levels l * primeAmplitude59970 p theta n) *
                  primeFrequency59970 p n = 0) →
              ∀ n : ℕ, theta n = 0

end

end MathlibPlus.Open.Formalization.ArithmeticKernels
