import Mathlib

open scoped BigOperators
open Filter
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000ea_dbd6_7a56_af5f_ee57b3e2d981

noncomputable def thetaShell (u : ℝ) : ℝ :=
  ∑' m : {m : ℕ // 1 ≤ m},
    Real.exp (-Real.pi * (m.1 : ℝ) ^ 2 * Real.exp (2 * u))

noncomputable def primitiveThetaMoment (n : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (u / 2) * thetaShell u * u ^ (2 * n)

noncomputable def primitiveNormalizedThetaMoment (n : ℕ) : ℝ :=
  2 * primitiveThetaMoment n / ((Nat.factorial (2 * n) : ℕ) : ℝ)

noncomputable def primitiveThetaRatio (n : ℕ) : ℝ :=
  primitiveNormalizedThetaMoment n /
    primitiveNormalizedThetaMoment (n - 1)

/-- Claim 9031: primitive completed-theta moments. -/
def primitiveCompletedThetaMoments9031 : Prop :=
  (∀ (u : ℝ),
      thetaShell u =
        ∑' m : {m : ℕ // 1 ≤ m},
          Real.exp (-Real.pi * (m.1 : ℝ) ^ 2 * Real.exp (2 * u))) ∧
    (∀ n : ℕ,
      primitiveThetaMoment n =
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (u / 2) * thetaShell u * u ^ (2 * n)) ∧
    (∀ n : ℕ,
      primitiveNormalizedThetaMoment n =
        2 * primitiveThetaMoment n /
          ((Nat.factorial (2 * n) : ℕ) : ℝ)) ∧
    (∀ n : ℕ,
      primitiveThetaRatio n =
        primitiveNormalizedThetaMoment n /
          primitiveNormalizedThetaMoment (n - 1))

noncomputable def fullThetaExpectation (n : {n : ℕ // 0 < n}) : ℝ :=
  (∫ u in Set.Ioi (0 : ℝ),
      u ^ 2 *
        (Real.exp (u / 2) * thetaShell u * u ^ (2 * (n.1 - 1)))) /
    primitiveThetaMoment (n.1 - 1)

/-- Claim 9036: the exact ratio/expectation identity. -/
def exactIntegralRatioIdentity9036 : Prop :=
  ∀ n : {n : ℕ // 0 < n},
    primitiveThetaMoment n.1 / primitiveThetaMoment (n.1 - 1) =
      fullThetaExpectation n

/-- The nonnegative real principal branch of the Lambert W relation. -/
noncomputable def lambertW0 (z : ℝ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = z}

noncomputable def lambertConsecutiveScale (n : ℕ) : ℝ :=
  lambertW0 (2 * (n : ℝ) / Real.pi) ^ 2 / (16 * (n : ℝ) ^ 2)

noncomputable def logarithmicConsecutiveScale (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2

/-- Claim 9037: Lambert-W consecutive-ratio law, order, and decay. -/
def lambertWConsecutiveRatioLaw9037 : Prop :=
  Tendsto
      (fun n : ℕ => primitiveThetaRatio n / lambertConsecutiveScale n)
      atTop (nhds 1) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        c * logarithmicConsecutiveScale n ≤ primitiveThetaRatio n ∧
          primitiveThetaRatio n ≤ C * logarithmicConsecutiveScale n) ∧
    Tendsto primitiveThetaRatio atTop (nhds 0)

noncomputable def realOrderThetaMoment (x : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (u / 2) * thetaShell u * Real.rpow u (2 * x)

noncomputable def firstShellPhase (x u : ℝ) : ℝ :=
  2 * x * Real.log u + u / 2 - Real.pi * Real.exp (2 * u)

noncomputable def firstShellMoment (x : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), Real.exp (firstShellPhase x u)

noncomputable def firstShellNormalizedLog (x : ℝ) : ℝ :=
  Real.log (2 * firstShellMoment x / Real.Gamma (2 * x + 1))

noncomputable def fullThetaNormalizedLog (x : ℝ) : ℝ :=
  Real.log (2 * realOrderThetaMoment x / Real.Gamma (2 * x + 1))

/-- Claim 9040: real-order primitive and first-shell moment definitions. -/
def realOrderPrimitiveThetaMoment9040 : Prop :=
  (∀ x : ℝ, 1 ≤ x →
      realOrderThetaMoment x =
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (u / 2) * thetaShell u * Real.rpow u (2 * x)) ∧
    (∀ x : ℝ, 1 ≤ x →
      firstShellMoment x =
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (2 * x * Real.log u + u / 2 -
            Real.pi * Real.exp (2 * u))) ∧
    (∀ x : ℝ, 1 ≤ x →
      firstShellNormalizedLog x =
        Real.log (2 * firstShellMoment x / Real.Gamma (2 * x + 1))) ∧
    (∀ n : ℕ,
      fullThetaNormalizedLog (n : ℝ) =
        Real.log (primitiveNormalizedThetaMoment n))

noncomputable def firstShellLogExpectation (x : ℝ) : ℝ :=
  (∫ u in Set.Ioi (0 : ℝ),
      Real.log u * Real.exp (firstShellPhase x u)) /
    firstShellMoment x

noncomputable def firstShellLogVariance (x : ℝ) : ℝ :=
  (∫ u in Set.Ioi (0 : ℝ),
      (Real.log u - firstShellLogExpectation x) ^ 2 *
        Real.exp (firstShellPhase x u)) /
    firstShellMoment x

/-- Claim 9042: differentiated first-shell moment identities. -/
def exactDifferentiatedMomentIdentities9042 : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    deriv (fun y : ℝ => Real.log (firstShellMoment y)) x =
        2 * firstShellLogExpectation x ∧
      deriv (fun y : ℝ => deriv
        (fun z : ℝ => Real.log (firstShellMoment z)) y) x =
        4 * firstShellLogVariance x

noncomputable def realOrderFSecondDerivative (x : ℝ) : ℝ :=
  deriv (fun y : ℝ => deriv firstShellNormalizedLog y) x

/-- Claim 9044: primitive-moment curvature law. -/
def primitiveMomentCurvatureLaw9044 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop,
      |realOrderFSecondDerivative x -
          (-2 / x * lambertW0 (2 * x / Real.pi) /
            (1 + lambertW0 (2 * x / Real.pi)))| ≤
        C * (1 / (x * lambertW0 (2 * x / Real.pi) ^ 2) + 1 / x ^ 2)

noncomputable def lambertGamma (n : ℕ) : ℝ :=
  lambertW0 (2 * (n : ℝ) / Real.pi) /
    (1 + lambertW0 (2 * (n : ℝ) / Real.pi))

noncomputable def normalizedShiftLog (n k : ℕ) : ℝ :=
  Real.log ((primitiveNormalizedThetaMoment (n + k) /
      primitiveNormalizedThetaMoment n) /
    (primitiveNormalizedThetaMoment (n + 1) /
      primitiveNormalizedThetaMoment n) ^ k)

noncomputable def mesoscopicErrorScale (n k : ℕ) : ℝ :=
  (k : ℝ) ^ 2 /
      ((n : ℝ) * lambertW0 (2 * (n : ℝ) / Real.pi) ^ 2) +
    (k : ℝ) ^ 3 / (n : ℝ) ^ 2

/-- Claim 9046: mesoscopic normalized-shift expansion. -/
def mesoscopicNormalizedShiftExpansion9046 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ → ℕ,
      Tendsto (fun n : ℕ =>
        (k n : ℝ) / Real.rpow (n : ℝ) (2 / 3 : ℝ))
        atTop (nhds 0) →
      ∀ᶠ n : ℕ in atTop,
        |normalizedShiftLog n (k n) +
            lambertGamma n / (n : ℝ) * (k n : ℝ) * ((k n : ℝ) - 1)| ≤
          C * mesoscopicErrorScale n (k n)

noncomputable def squareRootShift (x : ℝ) (n : ℕ) : ℕ :=
  ⌊x * Real.sqrt (n : ℝ)⌋₊

noncomputable def forwardShiftRatio (n k : ℕ) : ℝ :=
  (primitiveNormalizedThetaMoment (n + k) /
      primitiveNormalizedThetaMoment n) /
    (primitiveNormalizedThetaMoment (n + 1) /
      primitiveNormalizedThetaMoment n) ^ k

/-- Claim 9047: square-root-window Gaussian limit. -/
def squareRootWindowGaussianLimit9047 : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x : ℝ, 0 ≤ x → x ≤ A →
        |forwardShiftRatio n (squareRootShift x n) -
            Real.exp (-(x ^ 2))| < ε

noncomputable def rectangularShiftLog (n r s : ℕ) : ℝ :=
  Real.log ((primitiveNormalizedThetaMoment (n + r + s) *
      primitiveNormalizedThetaMoment n) /
    (primitiveNormalizedThetaMoment (n + r) *
      primitiveNormalizedThetaMoment (n + s)))

/-- Claim 9048: rectangular two-shift Hessian. -/
def rectangularTwoShiftHessian9048 : Prop :=
  ∀ R S : ℝ, 0 < R → 0 < S → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ r s : ℕ,
        (r : ℝ) ≤ R * Real.sqrt (n : ℝ) →
        (s : ℝ) ≤ S * Real.sqrt (n : ℝ) →
        |rectangularShiftLog n r s +
            2 * lambertGamma n * (r : ℝ) * (s : ℝ) / (n : ℝ)| < ε

noncomputable def mixedShiftLog (n r s : ℕ) : ℝ :=
  Real.log ((primitiveNormalizedThetaMoment (n - r + s) *
      primitiveNormalizedThetaMoment n) /
    (primitiveNormalizedThetaMoment (n - r) *
      primitiveNormalizedThetaMoment (n + s)))

noncomputable def mixedErrorScale (n r s : ℕ) : ℝ :=
  ((r + s : ℕ) : ℝ) ^ 2 /
      ((n : ℝ) * lambertW0 (2 * (n : ℝ) / Real.pi) ^ 2) +
    ((r + s : ℕ) : ℝ) ^ 3 / (n : ℝ) ^ 2

/-- Claim 9050: backward-forward mixed theta-shift law. -/
def backwardForwardMixedShiftLaw9050 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ r s : ℕ → ℕ,
      Tendsto (fun n : ℕ =>
        ((r n + s n : ℕ) : ℝ) /
          Real.rpow (n : ℝ) (2 / 3 : ℝ))
        atTop (nhds 0) →
      ∀ᶠ n : ℕ in atTop,
        r n ≤ n ∧
        |mixedShiftLog n (r n) (s n) -
            2 * lambertGamma n * (r n : ℝ) * (s n : ℝ) / (n : ℝ)| ≤
          C * mixedErrorScale n (r n) (s n)

/-- Claim 9051: exact rectangular curvature identity. -/
def exactRectangularCurvatureIdentity9051 : Prop :=
  ∀ x r s : ℝ, 0 ≤ r → 0 ≤ s →
    firstShellNormalizedLog (x - r + s) + firstShellNormalizedLog x -
        firstShellNormalizedLog (x - r) - firstShellNormalizedLog (x + s) =
      ∫ u in (-r)..0, ∫ v in 0..s,
        -realOrderFSecondDerivative (x + u + v)

noncomputable def mixedShiftRatio (n r s : ℕ) : ℝ :=
  (primitiveNormalizedThetaMoment (n - r + s) *
      primitiveNormalizedThetaMoment n) /
    (primitiveNormalizedThetaMoment (n - r) *
      primitiveNormalizedThetaMoment (n + s))

/-- Claim 9052: square-root mixed heat limit. -/
def squareRootMixedHeatLimit9052 : Prop :=
  ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ B →
        |mixedShiftRatio n (squareRootShift x n) (squareRootShift y n) -
            Real.exp (2 * x * y)| < ε

open Polynomial

noncomputable def intPolynomialEvalComplex
    (P : Polynomial ℤ) (x : ℂ) : ℂ :=
  Polynomial.eval₂ (Int.castRingHom ℂ) x P

noncomputable def reciprocalLiftRelation
    (Q P : Polynomial ℤ) (n : ℕ) : Prop :=
  Q.natDegree = n ∧
    ∀ x : ℂ, x ≠ 0 →
      intPolynomialEvalComplex P x =
        x ^ n * intPolynomialEvalComplex Q (x + x⁻¹)

/-- Claim 9151: monic reciprocal lift of doubled degree. -/
def reciprocalLiftMonicReciprocal9151 : Prop :=
  ∀ (Q : Polynomial ℤ) (n : ℕ), Q.Monic → Q.natDegree = n →
    ∃ P : Polynomial ℤ,
      P.Monic ∧ P.natDegree = 2 * n ∧ P.reverse = P ∧
        reciprocalLiftRelation Q P n

noncomputable def traceChebyshev (n : ℕ) : Polynomial ℤ :=
  (Nat.rec (motive := fun _ => Polynomial ℤ × Polynomial ℤ)
    (Polynomial.C 2, Polynomial.X)
    (fun _ p => (p.2, Polynomial.X * p.2 - p.1)) n).1

noncomputable def cyclicResultant
    (P : Polynomial ℤ) (m : ℕ) : ℤ :=
  Polynomial.resultant P (Polynomial.X ^ m - Polynomial.C 1)

/-- Claim 9153: exact Chebyshev resultant identity. -/
def exactChebyshevResultantIdentity9153 : Prop :=
  ∀ (Q P : Polynomial ℤ) (n : ℕ),
    Q.Monic → Q.natDegree = n → reciprocalLiftRelation Q P n →
      ∀ m : ℕ,
        cyclicResultant P m =
          Polynomial.resultant Q (Polynomial.C 2 - traceChebyshev m)

noncomputable def hasCyclotomicFactor (P : Polynomial ℤ) : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧ Polynomial.cyclotomic d ℤ ∣ P

/-- Claim 9154: cyclotomic factors and zero cyclic resultants. -/
def cyclotomicFactorsCauseResultantZeros9154 : Prop :=
  ∀ P : Polynomial ℤ,
    hasCyclotomicFactor P ↔
      ∃ m : ℕ, 1 ≤ m ∧ cyclicResultant P m = 0

noncomputable def cyclicResultantMagnitude
    (P : Polynomial ℤ) (m : ℕ) : ℕ :=
  Int.natAbs (cyclicResultant P m)

noncomputable def isNoncyclotomic (P : Polynomial ℤ) : Prop :=
  ¬hasCyclotomicFactor P

/-- Claim 9155: cyclic-resultant divisibility sequence. -/
def cyclicResultantsDivisibilitySequence9155 : Prop :=
  ∀ P : Polynomial ℤ, isNoncyclotomic P →
    (∀ m : ℕ, 1 ≤ m → 0 < cyclicResultantMagnitude P m) ∧
      (∀ m r : ℕ, 1 ≤ m → 1 ≤ r → m ∣ r →
        cyclicResultantMagnitude P m ∣ cyclicResultantMagnitude P r)

noncomputable def primitiveCyclotomicMagnitude
    (P : Polynomial ℤ) (m : ℕ) : ℕ :=
  Int.natAbs (Polynomial.resultant P (Polynomial.cyclotomic m ℤ))

/-- Claim 9156: primitive cyclotomic factorization. -/
def primitiveCyclotomicFactorization9156 : Prop :=
  ∀ (P : Polynomial ℤ) (m : ℕ), 1 ≤ m →
    cyclicResultantMagnitude P m =
      Finset.prod m.divisors
        (fun d => primitiveCyclotomicMagnitude P d)

end MathlibPlus.Open.ResearchFormalizationBatch_01a000ea_dbd6_7a56_af5f_ee57b3e2d981
