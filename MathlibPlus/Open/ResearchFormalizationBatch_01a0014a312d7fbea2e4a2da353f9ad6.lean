import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a0014a312d7fbea2e4a2da353f9ad6

/-! The staircase convention uses zero-based `Fin r` indices for the
    one-based partition parts in the packet. -/

def IsStaircasePartition (r : ℕ) (part : Fin r → ℕ) : Prop :=
  Antitone part ∧ ∀ i : Fin r, part i ≤ r - i.1

def staircaseDegree (r : ℕ) (part : Fin r → ℕ) (j : Fin r) : ℕ :=
  j.1 + part (Fin.rev j)

def outOfRangeBinomial (i n : ℕ) : ℤ :=
  if i ≤ n then (Nat.choose (i + 1) (n - i) : ℤ) else 0

def binomialPluckerCoordinate (r : ℕ) (part : Fin r → ℕ) : ℤ :=
  Matrix.det (fun i j : Fin r =>
    outOfRangeBinomial i.1 (staircaseDegree r part j))

/-- The two ordered products in the seed alternant identity. -/
def seedVandermonde (r : ℕ) (z : Fin r → ℂ) : ℂ :=
  ∏ a : Fin r, ∏ b ∈ Finset.Ioi a, (z b - z a)

def seedPairProduct (r : ℕ) (z : Fin r → ℂ) : ℂ :=
  ∏ a : Fin r, ∏ b ∈ Finset.Ioi a, (1 + z a + z b)

/-- Claim 9705: the seed alternant product identity. -/
def claim9705_seedAlternantProductIdentity : Prop :=
  ∀ (r : ℕ) (z : Fin r → ℂ),
    Matrix.det (fun i j : Fin r =>
      (z j) ^ i.1 * (1 + z j) ^ (i.1 + 1)) =
      seedVandermonde r z * (∏ j : Fin r, (1 + z j)) * seedPairProduct r z

/-- Claim 9710: every staircase binomial minor is strictly positive. -/
def claim9710_strictStaircaseBinomialMinorPositivity : Prop :=
  ∀ (r : ℕ), 1 ≤ r →
    ∀ (part : Fin r → ℕ), IsStaircasePartition r part →
      0 < binomialPluckerCoordinate r part

/-- Claim 9951. -/
def annularZeroMeanSourceClass (a R : ℝ) : Set (ℝ → ℝ) :=
  {f | ContDiff ℝ ⊤ f ∧ Even f ∧ HasCompactSupport f ∧
    Function.support f ⊆ Set.Icc (-R) (-a) ∪ Set.Icc a R ∧
    ∫ x, f x = 0}

/-- Claim 10418: reciprocal slope data and its mean do not force purity. -/
def claim10418_slopeDualityMeanSlopeOffPurity : Prop :=
  let slopes : Set ℚ := {1 / 3, 2 / 3}
  let q : ℝ := 9
  (∀ slope : ℚ, slope ∈ slopes → 1 - slope ∈ slopes) ∧
    ((1 / 3 : ℚ) + 2 / 3) / 2 = 1 / 2 ∧
    Real.rpow q (1 / 3 : ℝ) * Real.rpow q (2 / 3 : ℝ) = q ∧
    Real.rpow q (1 / 3 : ℝ) ≠ 3 ∧
    Real.rpow q (2 / 3 : ℝ) ≠ 3

/-- Claim 10422.  The quotient modules are recorded explicitly rather than
    replaced by a predicate carrying an arbitrary module. -/
def claim10422_determinantDoesNotRecoverJordanMultiplicityData : Prop :=
  let R := Polynomial ℂ
  let u : R := Polynomial.X
  let I : Ideal R := Ideal.span ({u} : Set R)
  let A : Matrix (Fin 2) (Fin 2) R :=
    !![u, 0; 0, u]
  let B : Matrix (Fin 2) (Fin 2) R :=
    !![u, 1; 0, u]
  let M₁ := (R ⧸ I) × (R ⧸ I)
  let M₂ := R ⧸ (Ideal.span ({u ^ 2} : Set R))
  Matrix.det A = u ^ 2 ∧
    Matrix.det B = u ^ 2 ∧
    ¬ Nonempty (M₁ ≃ₗ[R] M₂)

/-- Rising factorials used by the explicitly given Bezout and Kummer systems. -/
def risingReal (α : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (α + k)

def bezoutHReal (α : ℝ) (j : ℕ) : ℝ :=
  risingReal α j / (Nat.factorial (2 * j) : ℝ)

def completedBezoutSection (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (min i.1 j.1 + 1),
      ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) *
        bezoutHReal α a * bezoutHReal α (i.1 + j.1 + 1 - a)

def risingPoly (n : ℕ) : Polynomial ℚ :=
  ∏ k ∈ Finset.range n, (Polynomial.X + Polynomial.C (k : ℚ))

def bezoutHPoly (j : ℕ) : Polynomial ℚ :=
  Polynomial.C ((Nat.factorial (2 * j) : ℚ)⁻¹) * risingPoly j

def completedBezoutPoly (N : ℕ) : Matrix (Fin N) (Fin N) (Polynomial ℚ) :=
  fun i j =>
    ∑ a ∈ Finset.range (min i.1 j.1 + 1),
      Polynomial.C ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℚ) *
        bezoutHPoly a * bezoutHPoly (i.1 + j.1 + 1 - a)

def wallProduct (N : ℕ) (K : ℚ) : Polynomial ℚ :=
  Polynomial.C K *
    (∏ j ∈ Finset.range N,
      (Polynomial.X + Polynomial.C (j : ℚ)) ^ (N - j)) *
    (∏ k ∈ Finset.range (N - 1),
      (Polynomial.C (2 : ℚ) * Polynomial.X -
        Polynomial.C ((2 * k + 1 : ℕ) : ℚ)) ^ (N - (k + 1)))

/-- Claim 10511. -/
def claim10511_exactWallProductThroughRankTwelve : Prop :=
  ∀ N : ℕ, 1 ≤ N → N ≤ 12 →
    ∃ K : ℚ, 0 < K ∧
      Matrix.det (completedBezoutPoly N) = wallProduct N K

/-- Claim 10512.  The last conjunct is the stated finite interpolation
    certificate, with the distinct evaluation points made explicit. -/
def claim10512_degreeBoundInterpolationCertificate : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    (∀ i j : Fin N,
      (completedBezoutPoly N i j).natDegree = i.1 + j.1 + 1) ∧
    (∀ σ : Equiv.Perm (Fin N),
      (∏ i : Fin N, completedBezoutPoly N (σ i) i).natDegree = N ^ 2) ∧
    (completedBezoutPoly N).det.natDegree ≤ N ^ 2 ∧
    (∀ (P Q : Polynomial ℚ) (x : Fin (N ^ 2 + 1) → ℚ),
      P.natDegree ≤ N ^ 2 → Q.natDegree ≤ N ^ 2 →
      Function.Injective x →
      (∀ k, Polynomial.eval (x k) P = Polynomial.eval (x k) Q) →
      P = Q)

/-- Claim 10513. -/
def claim10513_consecutivePositiveChamberThroughRankTwelve : Prop :=
  ∀ (α : ℝ) (N : ℕ), 0 < α → 1 ≤ N → N ≤ 12 →
    ((∀ k : ℕ, 1 ≤ k → k ≤ N →
        0 < Matrix.det (completedBezoutSection α k)) ↔
      α > (N : ℝ) - 3 / 2)

def kummerA (α : ℝ) (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n =>
    risingReal (α + j) n /
      ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) *
        risingReal (2 * j + 1 / 2) n))

def kummerP (α : ℝ) (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n =>
    risingReal (α + j + 1) n /
      ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) *
        risingReal (2 * j + 3 / 2) n))

/-- Claim 10515. -/
def claim10515_shiftedKummerCoefficientSystems : Prop :=
  ∀ (α : ℝ) (j : ℕ),
    (PowerSeries.derivative ℝ) (kummerA α j) =
      ((α + j) / (2 * (4 * j + 1))) • kummerP α j

def shiftedGammaCell (α : ℝ) (p : ℕ) (u : ℝ) : ℝ :=
  u ^ p * Real.rpow u (α - 1) * Real.exp (-u) / Real.Gamma α

def shiftedGammaCellJet (α : ℝ) (p q : ℕ) : ℝ :=
  MeasureTheory.integral
    (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun u => u ^ q * shiftedGammaCell α p u)

/-- Claim 10525. -/
def claim10525_shiftedGammaCellJetRealization : Prop :=
  ∀ (α : ℝ) (p q : ℕ), 0 < α →
    shiftedGammaCellJet α p q = risingReal α (p + q) ∧
    (∀ u : ℝ, 0 < u → 0 < shiftedGammaCell α p u)

def endpointPacketPolynomial (β s : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 =>
      (Polynomial.C β - Polynomial.C s * Polynomial.X) *
          endpointPacketPolynomial β s k +
        Polynomial.C s * Polynomial.X *
          (Polynomial.derivative) (endpointPacketPolynomial β s k)

/-- Claim 10530. -/
def claim10530_endpointPacketDerivativeRecurrence : Prop :=
  (∀ (β s : ℝ) (k : ℕ),
      endpointPacketPolynomial β s (k + 1) =
        (Polynomial.C β - Polynomial.C s * Polynomial.X) *
            endpointPacketPolynomial β s k +
          Polynomial.C s * Polynomial.X *
            (Polynomial.derivative) (endpointPacketPolynomial β s k)) ∧
  (∀ (β s q t : ℝ) (k : ℕ),
      iteratedDeriv k (fun x : ℝ =>
        Real.exp (β * x - q * Real.exp (s * x))) t =
        Real.exp (β * t - q * Real.exp (s * t)) *
          Polynomial.eval (q * Real.exp (s * t))
            (endpointPacketPolynomial β s k))

/-- The divisor sum in Claim 10920, written with the unique complementary
    divisor `n / a`.  The argument is positive by construction. -/
def principalSeriesTau (x : ℝ) (n : ℕ) : ℂ :=
  ∑ a ∈ (n + 1).divisors,
    Complex.cpow
      ((a : ℂ) / (((n + 1) / a : ℕ) : ℂ)) (Complex.I * x)

def principalSeriesD (s x y : ℝ) : ℂ :=
  ∑' n : ℕ,
    principalSeriesTau x n * principalSeriesTau y n *
      Complex.cpow (n + 1 : ℂ) (-s)

def complexKernelPSD (K : ℝ → ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    let q := ∑ i : Fin n, ∑ j : Fin n,
      star (c i) * K (x i) (x j) * c j
    Complex.im q = 0 ∧ 0 ≤ Complex.re q

/-- Claim 10920. -/
def claim10920_polarizedPrincipalSeriesRankinGram : Prop :=
  ∀ (s : ℝ), 1 < s →
    complexKernelPSD (principalSeriesD s) ∧
    (∀ x y : ℝ,
      principalSeriesD s x y =
        riemannZeta (s + Complex.I * (x + y)) *
          riemannZeta (s + Complex.I * (x - y)) *
          riemannZeta (s - Complex.I * (x - y)) *
          riemannZeta (s - Complex.I * (x + y)) /
          riemannZeta (2 * s)) ∧
    (∀ x : ℝ,
      principalSeriesD s x x =
        riemannZeta (s - 2 * Complex.I * x) *
          riemannZeta (s + 2 * Complex.I * x) *
          riemannZeta s ^ 2 /
          riemannZeta (2 * s))

end MathlibPlus.Open.ResearchFormalizationBatch_01a0014a312d7fbea2e4a2da353f9ad6
