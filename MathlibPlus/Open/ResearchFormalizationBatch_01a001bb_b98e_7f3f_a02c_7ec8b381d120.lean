import Mathlib

open scoped BigOperators
open Set Filter Topology MeasureTheory

namespace MathlibPlus
namespace Open
namespace ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

/-! Exact carriers used by the admitted statements.  The declarations below are
proof-free formal statement nodes; the auxiliary definitions only spell out
notation that occurs in those statements. -/

noncomputable section

/-- The integer Möbius function, written without relying on a library name. -/
def mobiusInt (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if (n.primeFactors.filter (fun p => p ^ 2 ∣ n)).Nonempty then 0
  else (-1 : ℤ) ^ n.primeFactors.card

def mobiusReal (n : ℕ) : ℝ := (mobiusInt n : ℝ)

def squarefreeNat (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ^ 2 ∣ n

/-- A standard generalized binomial coefficient. -/
def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (a - (j : ℝ)) / ((j + 1 : ℕ) : ℝ)

def generalizedLaguerre (m : ℕ) (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * generalizedBinomial ((m : ℝ) + a) (m - k) * x ^ k /
      (k.factorial : ℝ)

def heatKernel (u t : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / (4 * t)) / (2 * Real.sqrt (Real.pi * t))

def heatDerivativeKernel (m : ℕ) (t u : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * iteratedDeriv m (fun s : ℝ => heatKernel u s) t

def heatKernelUDerivative (m : ℕ) (t u : ℝ) : ℝ :=
  iteratedDeriv 1 (fun v : ℝ => heatDerivativeKernel m t v) u

def claim7818 : Prop :=
  ∀ (m : ℕ) (t u : ℝ), 0 < t → 0 ≤ u →
    heatDerivativeKernel m t u =
      (m.factorial : ℝ) / (2 * Real.sqrt Real.pi) *
        Real.rpow t (- (m : ℝ) - 1 / 2) *
        Real.exp (-u ^ 2 / (4 * t)) *
        generalizedLaguerre m (-1 / 2) (u ^ 2 / (4 * t)) ∧
    heatKernelUDerivative m t u =
      -(m.factorial : ℝ) * u / (4 * Real.sqrt Real.pi) *
        Real.rpow t (- (m : ℝ) - 3 / 2) *
        Real.exp (-u ^ 2 / (4 * t)) *
        generalizedLaguerre m (1 / 2) (u ^ 2 / (4 * t))

/-- The complete confluent flag from the packet. -/
def confluentFlag (K : ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m => iteratedDeriv (i.val + j.val) K t)

def translationMinor (K : ℝ → ℝ) {q : ℕ} (x y : Fin q → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin q => K (x i - y j))

def claim3253 : Prop :=
  ∀ (K : ℝ → ℝ) (r : ℕ),
    (∀ m, 1 ≤ m → m ≤ r → ∀ t : ℝ, 0 < confluentFlag K m t) →
      ∀ q, 1 ≤ q → q ≤ r →
        ∀ (x y : Fin q → ℝ), StrictMono x → StrictMono y →
          0 < translationMinor K x y

/-- Dyadic complex powers use the real logarithm of the positive base 2. -/
def dyadicPower (s : ℂ) : ℂ := Complex.exp (s * (Real.log 2 : ℂ))

def dyadicJ (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then dyadicPower (s - 1)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then dyadicPower (-s)
    else 0

def dyadicHasEigenvalue (A : Matrix (Fin 2) (Fin 2) ℂ) (lam : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ A.mulVec v = lam • v

def dyadicSpectrum (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ lam : ℂ, dyadicHasEigenvalue A lam ↔
    lam = (1 / Real.sqrt 2 : ℂ) ∨ lam = (-1 / Real.sqrt 2 : ℂ)

def complexPositiveDefinite (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Matrix.IsHermitian A ∧
    ∀ v : Fin 2 → ℂ, v ≠ 0 →
      0 < (∑ i, (starRingEnd ℂ (v i)) * (A.mulVec v) i).re

def claim7803 : Prop :=
  ∀ s : ℂ,
    dyadicJ s * dyadicJ s = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    Matrix.det (dyadicJ s) = (-1 / 2 : ℂ) ∧
    (s.re = 1 / 2 →
      Matrix.IsHermitian (dyadicJ s) ∧
      dyadicSpectrum (dyadicJ s) ∧
      (Real.sqrt 2 : ℂ) • (dyadicJ s) * ((Real.sqrt 2 : ℂ) • dyadicJ s) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ))

def claim7804 : Prop :=
  ∀ s : ℂ, Matrix.IsHermitian (dyadicJ s) ↔ s.re = 1 / 2

def dyadicG (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + dyadicJ s

def claim7811 : Prop :=
  ∀ s : ℂ,
    (complexPositiveDefinite (dyadicG s) ↔ s.re = 1 / 2) ∧
      (s.re = 1 / 2 →
        ∀ lam : ℂ, dyadicHasEigenvalue (dyadicG s) lam ↔
          lam = 1 + (1 / Real.sqrt 2 : ℂ) ∨
          lam = 1 + (-1 / Real.sqrt 2 : ℂ))

/-- The normalized multiplier in the two asymptotic regimes. -/
def normalizedMultiplier (m : ℕ) (τ : ℝ) : ℝ :=
  Real.exp (2 * (m : ℝ)) /
      (8 * (m : ℝ) ^ (2 * m + 2) * Real.cosh (Real.pi * τ / 2)) *
    ∏ j ∈ Finset.range m,
      (((j + 1 : ℕ) : ℝ) ^ 2 + τ ^ 2 / 4)

def claim7832 : Prop :=
  (∀ τ : ℝ,
    Tendsto
      (fun m : ℕ => (m : ℝ) * normalizedMultiplier m τ) atTop
      (𝓝 (if τ = 0 then Real.pi / 4 else Real.tanh (Real.pi * τ / 2) / (2 * τ)))) ∧
  (∀ y : ℝ,
    Tendsto
      (fun m : ℕ => (m : ℝ)⁻¹ *
        Real.log (normalizedMultiplier m (2 * (m : ℝ) * y))) atTop
      (𝓝 (Real.log (1 + y ^ 2) - 2 * |y| * Real.arctan |y|))) ∧
  (∀ y : ℝ, y ≠ 0 →
    Real.log (1 + y ^ 2) - 2 * |y| * Real.arctan |y| < 0)

def normalizedCoefficient (a₀ : ℝ) (e : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then e n.toNat else 0

def reciprocalCoefficient (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      -∑ i ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (i + 1) * e (i + 1) * reciprocalCoefficient e (n - i)

def toeplitzDet (a₀ : ℝ) (e : ℕ → ℝ) (r k : ℕ) : ℝ :=
  a₀ ^ r * Matrix.det (fun i j : Fin r =>
    normalizedCoefficient a₀ e (k + j.val - i.val : ℤ))

def reciprocalToeplitzDet (e : ℕ → ℝ) (r k : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin k =>
    normalizedCoefficient 1 (reciprocalCoefficient e)
      (r + j.val - i.val : ℤ))

def claim7954 : Prop :=
  ∀ (a₀ : ℝ) (e : ℕ → ℝ), a₀ > 0 → e 0 = 1 →
    (∀ n : ℤ, n < 0 → normalizedCoefficient a₀ e n = 0) ∧
    (∀ n : ℕ,
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ i * e i * reciprocalCoefficient e (n - i) =
          if n = 0 then 1 else 0) ∧
    (∀ r k : ℕ, 1 ≤ r → 1 ≤ k →
      toeplitzDet a₀ e r k =
        Matrix.det (fun i j : Fin r =>
          a₀ * normalizedCoefficient a₀ e (k + j.val - i.val : ℤ)))

def claim7955 : Prop :=
  ∀ (a₀ : ℝ) (e : ℕ → ℝ) (r k : ℕ),
    a₀ > 0 → e 0 = 1 → 1 ≤ r → 1 ≤ k →
    toeplitzDet a₀ e r k / a₀ ^ r =
      Matrix.det (fun i j : Fin r =>
        normalizedCoefficient a₀ e (k + j.val - i.val : ℤ)) ∧
    toeplitzDet a₀ e r k / a₀ ^ r = reciprocalToeplitzDet e r k

/-- Recurrence and Hankel notation used by the admitted recurrence claims. -/
def recurrenceOperator (q : ℕ) (w : Fin q → ℂ) (p : ℕ → ℂ) (n : ℕ) : ℂ :=
  p (n + q) + ∑ j : Fin q, w j * p (n + j.val)

def minimalRecurrence (p : ℕ → ℂ) (q : ℕ) (w : Fin q → ℂ) : Prop :=
  (∀ n, recurrenceOperator q w p n = 0) ∧
    (∀ q' : ℕ, q' < q →
      ∀ v : Fin q' → ℂ,
        (∀ n, recurrenceOperator q' v p n = 0) → False)

def hankelMatrix (p : ℕ → ℂ) (n q : ℕ) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ :=
  fun i j => p (n + i.val + j.val)

def consecutiveHankel (p : ℕ → ℂ) (n q : ℕ) : ℂ :=
  Matrix.det (fun i j : Fin q => p (n + i.val + j.val))

def recurrenceVector (q : ℕ) (w : Fin q → ℂ) : Fin (q + 1) → ℂ :=
  fun i => if h : i.val < q then w ⟨i.val, h⟩ else 1

def recurrencePolynomial (q : ℕ) (w : Fin q → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ q + ∑ j : Fin q, Polynomial.C (w j) * Polynomial.X ^ j.val

def variationPolynomial (p f : ℕ → ℂ) (n q : ℕ) : Polynomial ℂ :=
  Matrix.det (fun i j : Fin (q + 1) =>
    Polynomial.C (p (n + i.val + j.val)) +
      Polynomial.X * Polynomial.C (f (n + i.val + j.val)))

/-- The same operator written without pipeline notation, for readability. -/
def squaredRecurrence' (q : ℕ) (w : Fin q → ℂ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  recurrenceOperator q w (fun m => recurrenceOperator q w f m) n

def claim7968 : Prop :=
  ∀ (p : ℕ → ℂ) (q n : ℕ) (w : Fin q → ℂ),
    minimalRecurrence p q w → consecutiveHankel p n q ≠ 0 →
      let H := hankelMatrix p n q
      let v := recurrenceVector q w
      H.mulVec v = 0 ∧
      (Matrix.transpose H).mulVec v = 0 ∧
      Matrix.rank H = q ∧
      Matrix.adjugate H = fun i j => consecutiveHankel p n q * v i * v j

def claim7969 : Prop :=
  ∀ (p : ℕ → ℂ) (q n : ℕ) (w : Fin q → ℂ),
    minimalRecurrence p q w → consecutiveHankel p n q ≠ 0 →
      ∀ f : ℕ → ℂ,
        (variationPolynomial p f n q).coeff 1 =
          consecutiveHankel p n q * squaredRecurrence' q w f n

def claim7970 : Prop :=
  ∀ (p : ℕ → ℂ) (q n : ℕ) (w : Fin q → ℂ),
    ∀ hq : 0 < q, minimalRecurrence p q w →
      consecutiveHankel p (n + 1) q =
        (-1 : ℂ) ^ q * w ⟨0, hq⟩ * consecutiveHankel p n q

def exponentialPolynomial (N : ℕ) (Q : Fin N → Polynomial ℂ)
    (x : Fin N → ℂ) (n : ℕ) : ℂ :=
  ∑ i : Fin N, (Q i).eval (n : ℂ) * (x i) ^ n

def annihilator (x : ℂ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f (n + 1) - x * f n

def annihilatorPower (r : ℕ) (x : ℂ) (f : ℕ → ℂ) : ℕ → ℂ :=
  Nat.rec f (fun _ g n => annihilator x g n) r


def claim7971 : Prop :=
  ∀ (N : ℕ) (Q : Fin N → Polynomial ℂ) (x : Fin N → ℂ)
    (m : Fin N → ℕ),
    (∀ i, 0 < m i ∧ Q i ≠ 0 ∧ (Q i).natDegree = m i - 1 ∧
      (Q i).coeff ((Q i).natDegree) ≠ 0) →
    (∀ i j, i ≠ j → x i ≠ x j) →
    (∀ i, x i ≠ 0) →
    let q := ∑ i : Fin N, m i
    let p := exponentialPolynomial N Q x
    let P := ∏ i : Fin N, (Polynomial.X - Polynomial.C (x i)) ^ m i
    ∃ w : Fin q → ℂ,
      recurrencePolynomial q w = P ∧
      minimalRecurrence p q w ∧
      (∀ n, consecutiveHankel p n q ≠ 0) ∧
      (∀ n, consecutiveHankel p (n + 1) q =
        (∏ i : Fin N, (x i) ^ m i) * consecutiveHankel p n q)

def doubleMode (a b x : ℂ) (n : ℕ) : ℂ :=
  (a + b * (n : ℂ)) * x ^ n

def claim7972 : Prop :=
  ∀ (a b x : ℂ), b ≠ 0 → x ≠ 0 →
    ∀ (f : ℕ → ℂ) (n : ℕ),
      (variationPolynomial (doubleMode a b x) f n 2).coeff 1 =
        -b ^ 2 * x ^ (2 * n + 2) * annihilatorPower 4 x f n

/-- One-sided Toeplitz minors, with the negative coefficients extended by zero. -/
def oneSidedToeplitzEntry (f : ℕ → ℝ) (r c : ℕ) : ℝ :=
  if c < r then 0 else f (c - r)

def oneSidedToeplitzMinor (f : ℕ → ℝ) {p : ℕ}
    (r c : Fin p → ℕ) : ℝ :=
  Matrix.det (fun i j : Fin p => oneSidedToeplitzEntry f (r i) (c j))

def claim8190 : Prop :=
  ∀ (p : ℕ) (r c : Fin p → ℕ), StrictMono r → StrictMono c →
    ((∃ f : ℕ → ℝ, oneSidedToeplitzMinor f r c ≠ 0) ↔
      ∀ j : Fin p, r j ≤ c j)

def pfThrough (f : ℕ → ℝ) (s : ℕ) : Prop :=
  ∀ q : ℕ, q ≤ s →
    ∀ (r c : Fin q → ℕ), StrictMono r → StrictMono c →
      0 ≤ oneSidedToeplitzMinor f r c

def entireCoefficientSequence (f : ℕ → ℝ) : Prop :=
  ∀ z : ℂ, Summable (fun n : ℕ => (f n : ℂ) * z ^ n)

def nonPolynomialSequence (f : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ f n ≠ 0

def claim8191 : Prop :=
  ∀ (f : ℕ → ℝ) (p : ℕ),
    entireCoefficientSequence f →
    nonPolynomialSequence f →
    (∀ n, 0 < f n) →
    pfThrough f (p + 1) →
    ∀ (r c : Fin p → ℕ), StrictMono r → StrictMono c →
      (∀ j : Fin p, r j ≤ c j) → 0 < oneSidedToeplitzMinor f r c

/-- Jordan's totient and the finite divisor sums in the packet. -/
def jordanTotient (k n : ℕ) : ℝ :=
  (n : ℝ) ^ k * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ) ^ k)⁻¹)

def jordanDivisorRecombination (k n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors,
    mobiusReal (n / a) / ((a : ℝ) * (n / a : ℝ)) * (a : ℝ) ^ k

def mobiusDivisorSum (k n : ℕ) : ℝ :=
  ∑ b ∈ n.divisors, mobiusReal b / (b : ℝ) ^ k

def claim8290 : Prop :=
  (∀ (k n : ℕ), 1 ≤ k → 1 ≤ n →
    jordanDivisorRecombination k n =
      (n : ℝ) ^ (k - 1) * mobiusDivisorSum k n ∧
    jordanDivisorRecombination k n = jordanTotient k n / n) ∧
  (∀ n : ℕ, 1 ≤ n →
    (1 / (n : ℝ)) * ∑ b ∈ n.divisors, mobiusReal b =
      if n = 1 then 1 else 0)

def exponentialPowerSum (k : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then
    (n : ℝ) ^ (k - 1) * Real.exp (-x * n) else 0

def claim8292 : Prop :=
  ∀ (k n : ℕ) (x : ℝ), 1 ≤ k → 1 ≤ n → 0 < x →
    jordanTotient k n / n ≤ (n : ℝ) ^ (k - 1) ∧
    exponentialPowerSum k x ≤
      ((k - 1).factorial : ℝ) * Real.exp (-x) /
        (1 - Real.exp (-x)) ^ k

def absoluteVariation (N : ℕ) (lam u : ℝ) : ℝ :=
  ∑' a : ℕ, ∑' b : ℕ,
    if 0 < a ∧ 0 < b ∧ Nat.Coprime (a * b) N then
      mobiusReal b ^ 2 / ((a : ℝ) * b) * Real.exp (-u * a - u * lam * (a * b))
    else 0

def claim8297 : Prop :=
  ∀ (N : ℕ), squarefreeNat N →
    ∀ lam : ℝ, 0 < lam →
      ∃ c u₀ : ℝ, 0 < c ∧ 0 < u₀ ∧
        ∀ u : ℝ, 0 < u → u < u₀ →
          c * (Real.log (1 / u)) ^ 2 ≤ absoluteVariation N lam u

def divisorDelta (k : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ k.divisors, mobiusReal d * (Real.exp (-y * d) - 1)

def divisorDeltaExponential (k : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ k.divisors, mobiusReal d * Real.exp (-y * d)

def weightedDeltaNorm (δ : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, if 1 ≤ k then |δ k| ^ 2 / (k : ℝ) ^ 2 else 0

def claim8318 : Prop :=
  ∀ y : ℝ, 0 < y → y ≤ 1 →
    (∀ k : ℕ, 1 ≤ k →
      divisorDelta k y = divisorDeltaExponential k y - if k = 1 then 1 else 0) ∧
    weightedDeltaNorm (fun k => divisorDelta k y) ≤ 32 * y

def profileDelta (f : ℝ → ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ k.divisors, mobiusReal d * (f (y * d) - f 0)

def claim8319 : Prop :=
  ∀ (f : ℝ → ℝ) (A : ℝ),
    (∀ x : ℝ, 0 ≤ x → |f x - f 0| ≤ A * min x 1) →
    ∀ y : ℝ, 0 < y → y ≤ 1 →
      weightedDeltaNorm (fun k => profileDelta f k y) ≤ 32 * A ^ 2 * y

/-- The exponential specialization is stated independently, with all notation expanded. -/
def claim8378 : Prop :=
  ∀ (k : ℕ) (y : ℝ),
    profileDelta (fun x : ℝ => Real.exp (-x)) k y =
      divisorDeltaExponential k y - if k = 1 then 1 else 0

def zetaTwo : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then 1 / (n : ℝ) ^ 2 else 0

def squarefreeCoprimeCount (q X : ℕ) : ℝ :=
  ∑ g ∈ Finset.range (X + 1),
    if Nat.Coprime g q then mobiusReal g ^ 2 else 0

def claim8380 : Prop :=
  ∀ q : ℕ, squarefreeNat q →
    Tendsto
      (fun X : ℕ => squarefreeCoprimeCount q X /
        ((X : ℝ) / zetaTwo *
          ∏ p ∈ q.primeFactors, (1 + (p : ℝ)⁻¹)⁻¹)) atTop (𝓝 1)

def claim8381 : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
      ((Real.exp (-a * t) - 1) * (Real.exp (-b * t) - 1)) / t ^ 2) =
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b

def antiDiagonalMatrix (p : ℕ) (a d : ZMod p) :
    Matrix (Fin 2) (Fin 2) (ZMod p) :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then a
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then d
    else 0

def matrixImageSubmodule (p : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    Submodule (ZMod p) (Fin 2 → ZMod p) :=
  LinearMap.range (Matrix.mulVecLin M)

def claim33294 : Prop :=
  ∀ (p : ℕ), p.Prime → p % 2 = 1 →
    ∀ (a d : ZMod p), a ≠ 0 → d ≠ 0 →
      let M := antiDiagonalMatrix p a d
      ∀ V : Submodule (ZMod p) (Fin 2 → ZMod p),
        Module.finrank (ZMod p) V = 1 →
        matrixImageSubmodule p (M - 1) ≤ V →
          Matrix.rank (M - 1) ≤ 1 ∧
          Matrix.det (M - 1) = 0 ∧
          a * d = 1 ∧
          M * M = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) ∧
          (M ≠ (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) →
            matrixImageSubmodule p (M - 1) =
                LinearMap.ker (Matrix.mulVecLin (M + 1)) ∧
            Module.finrank (ZMod p) (matrixImageSubmodule p (M - 1)) = 1 ∧
            matrixImageSubmodule p (M - 1) = V)

/-- Planar configuration notation for the diameter-ratio claims. -/
def planarVector := Fin 2 → ℝ

def planarSub (u v : planarVector) : planarVector := fun i => u i - v i

def planarAdd (u v : planarVector) : planarVector := fun i => u i + v i

def planarSmul (c : ℝ) (u : planarVector) : planarVector := fun i => c * u i

def planarDot (u v : planarVector) : ℝ := ∑ i, u i * v i

def planarQ (u v : planarVector) : ℝ := planarDot (planarSub u v) (planarSub u v)

def planarPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2)

def planarPairQ {n : ℕ} (x : Fin n → planarVector)
    (p : Fin n × Fin n) : ℝ := planarQ (x p.1) (x p.2)

def planarValues {n : ℕ} (x : Fin n → planarVector) : Finset ℝ :=
  (planarPairs n).image (planarPairQ x)

def finsetMaxValue {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

def finsetMinValue {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

def planarPairMax {n : ℕ} (x : Fin n → planarVector) : ℝ :=
  finsetMaxValue (planarPairs n) (planarPairQ x)

def planarPairMin {n : ℕ} (x : Fin n → planarVector) : ℝ :=
  finsetMinValue (planarPairs n) (planarPairQ x)

def planarPhi {n : ℕ} (x : Fin n → planarVector) : ℝ :=
  Real.log (planarPairMax x) - Real.log (planarPairMin x)

def planarClosestPairs {n : ℕ} (x : Fin n → planarVector) :
    Finset (Fin n × Fin n) :=
  (planarPairs n).filter (fun p => planarPairQ x p = planarPairMin x)

def planarFarthestPairs {n : ℕ} (x : Fin n → planarVector) :
    Finset (Fin n × Fin n) :=
  (planarPairs n).filter (fun p => planarPairQ x p = planarPairMax x)

def planarDiameter {n : ℕ} (x : Fin n → planarVector) : ℝ :=
  Real.sqrt (planarPairMax x)

def planarDistinct {n : ℕ} (x : Fin n → planarVector) : Prop :=
  ∀ i j, i ≠ j → x i ≠ x j

def planarConfigDistance {n : ℕ} (x y : Fin n → planarVector) : ℝ :=
  Real.sqrt (∑ i, planarQ (x i) (y i))

def planarLocalMinimum {n : ℕ} (x : Fin n → planarVector) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ y : Fin n → planarVector,
      planarConfigDistance x y < ε → planarPhi x ≤ planarPhi y

def planarVelocityValue {n : ℕ} (x w : Fin n → planarVector)
    (p : Fin n × Fin n) : ℝ :=
  2 * planarDot (planarSub (x p.1) (x p.2))
      (planarSub (w p.1) (w p.2)) /
    planarPairQ x p

def planarLine {n : ℕ} (x w : Fin n → planarVector) (t : ℝ) :
    Fin n → planarVector :=
  fun i => planarAdd (x i) (planarSmul t (w i))

def claim33690 : Prop :=
  ∀ (n : ℕ) (x : Fin n → planarVector),
    2 ≤ n → planarDistinct x → planarPairMin x = 1 →
      planarPhi x = Real.log (planarPairMax x) - Real.log 1 ∧
      planarDiameter x = Real.sqrt (planarPairMax x) ∧
      planarClosestPairs x =
        (planarPairs n).filter (fun p => planarPairQ x p = planarPairMin x) ∧
      planarFarthestPairs x =
        (planarPairs n).filter (fun p => planarPairQ x p = planarPairMax x) ∧
      ∀ c : ℝ, c ≠ 0 →
        planarPhi (fun i => planarSmul c (x i)) = planarPhi x

def planarMaxVelocity {n : ℕ} (x w : Fin n → planarVector) : ℝ :=
  finsetMaxValue (planarFarthestPairs x) (planarVelocityValue x w)

def planarMinVelocity {n : ℕ} (x w : Fin n → planarVector) : ℝ :=
  finsetMinValue (planarClosestPairs x) (planarVelocityValue x w)

def claim33694 : Prop :=
  ∀ (n : ℕ) (x : Fin n → planarVector),
    2 ≤ n → planarDistinct x →
      ∀ w : Fin n → planarVector,
        Tendsto
            (fun t : ℝ =>
              (planarPhi (planarLine x w t) - planarPhi x) / t)
            (nhdsWithin 0 (Set.Ioi 0))
            (𝓝 (planarMaxVelocity x w - planarMinVelocity x w)) ∧
        (planarLocalMinimum x →
          0 ≤ planarMaxVelocity x w - planarMinVelocity x w)

def probabilityWeight {α : Type} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) : Prop :=
  (∀ z, z ∉ s → a z = 0) ∧
  (∀ z ∈ s, 0 ≤ a z) ∧
  (∑ z ∈ s, a z) = 1

def claim33698 : Prop :=
  ∀ (n : ℕ) (x : Fin n → planarVector),
    2 ≤ n → planarDistinct x → planarLocalMinimum x →
      ∃ α β : (Fin n × Fin n) → ℝ,
        probabilityWeight (planarClosestPairs x) α ∧
        probabilityWeight (planarFarthestPairs x) β ∧
        ∀ w : Fin n → planarVector,
          ∑ p ∈ planarClosestPairs x, α p * planarVelocityValue x w p =
            ∑ p ∈ planarFarthestPairs x, β p * planarVelocityValue x w p

def bigOAtZero (f g : ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ t : ℝ, |t| < δ → |f t| ≤ C * |g t|

def planarSecondCoefficient {n : ℕ} (x w : Fin n → planarVector)
    (p : Fin n × Fin n) : ℝ :=
  planarQ (w p.1) (w p.2) / planarPairQ x p -
    planarVelocityValue x w p ^ 2 / 2

def planarCriticalFarthest {n : ℕ} (x w : Fin n → planarVector) :
    Finset (Fin n × Fin n) :=
  (planarFarthestPairs x).filter
    (fun p => planarVelocityValue x w p = planarMaxVelocity x w)

def planarCriticalClosest {n : ℕ} (x w : Fin n → planarVector) :
    Finset (Fin n × Fin n) :=
  (planarClosestPairs x).filter
    (fun p => planarVelocityValue x w p = planarMinVelocity x w)

def claim33717 : Prop :=
  ∀ (n : ℕ) (x : Fin n → planarVector),
    2 ≤ n → planarDistinct x → planarLocalMinimum x →
      ∀ w : Fin n → planarVector,
        planarMaxVelocity x w = planarMinVelocity x w →
          (∀ p : Fin n × Fin n, p ∈ planarPairs n →
            bigOAtZero
              (fun t =>
                Real.log (planarPairQ (planarLine x w t) p) -
                  Real.log (planarPairQ x p) -
                  t * planarVelocityValue x w p -
                  t ^ 2 * planarSecondCoefficient x w p)
              (fun t => t ^ 3)) ∧
          finsetMaxValue (planarCriticalFarthest x w)
                (fun p => planarQ (w p.1) (w p.2)) /
              (planarDiameter x) ^ 2 ≥
            finsetMinValue (planarCriticalClosest x w)
              (fun p => planarQ (w p.1) (w p.2))

def regularRadius (m : ℕ) : ℝ :=
  1 / (2 * Real.sin (Real.pi / m))

def regularVertex (m : ℕ) (j : Fin m) : planarVector :=
  ![regularRadius m * Real.cos (2 * Real.pi * (j.val : ℝ) / m),
    regularRadius m * Real.sin (2 * Real.pi * (j.val : ℝ) / m)]

def regularPolygon (m : ℕ) : Fin m → planarVector := regularVertex m

def sideRelation {m : ℕ} (a b : Fin m) : Prop :=
  Nat.ModEq m (a.val + 1) b.val ∨ Nat.ModEq m (b.val + 1) a.val

def farthestRelation {m : ℕ} (k : ℕ) (a b : Fin m) : Prop :=
  Nat.ModEq m (a.val + k) b.val ∨ Nat.ModEq m (b.val + k) a.val

def cycleGraph {m : ℕ} (r : Fin m → Fin m → Prop) : Prop :=
  (∀ a, ¬ r a a) ∧
  (∀ a b, r a b → r b a) ∧
  (∀ a, ∃ b c, b ≠ c ∧ r a b ∧ r a c ∧
    ∀ d, r a d → d = b ∨ d = c) ∧
  (∀ a b, Relation.ReflTransGen r a b)

def triangleFree {m : ℕ} (r : Fin m → Fin m → Prop) : Prop :=
  ∀ a b c, r a b → r b c → r c a →
    a = b ∨ b = c ∨ c = a

def claim33807 : Prop :=
  ∀ (m : ℕ), 7 ≤ m → Odd m →
    let k := (m - 1) / 2
    let x := regularPolygon m
    Nat.Coprime k m ∧
      cycleGraph (sideRelation (m := m)) ∧
      triangleFree (sideRelation (m := m)) ∧
      cycleGraph (farthestRelation (m := m) k) ∧
      (∀ p : Fin m × Fin m, p ∈ planarPairs m →
        (planarPairQ x p = 1 ↔ sideRelation p.1 p.2)) ∧
      (∀ p : Fin m × Fin m, p ∈ planarPairs m →
        (planarPairQ x p = planarPairMax x ↔ farthestRelation k p.1 p.2)) ∧
      planarDiameter x =
        Real.sin (Real.pi * k / m) / Real.sin (Real.pi / m)

end
end ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120
end Open
end MathlibPlus
