import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-- The explicit reserve in the two-zero endpoint inequality. -/
def endpointReserve (a g : ℝ) : ℝ :=
  (3 * g ^ 2 + 2 * a ^ 2) / (a ^ 2 + g ^ 2) ^ 2

/-- The explicit two-zero expression from the admitted claim. -/
def twoZeroExpression (a g x : ℝ) : ℝ :=
  x ^ 2 / (a ^ 2 + x ^ 2) ^ 2
    + (g - x) ^ 2 / (a ^ 2 + (g - x) ^ 2) ^ 2
    + 2 * a ^ 2 / ((a ^ 2 + x ^ 2) * (a ^ 2 + (g - x) ^ 2))

/-- Claim 11334: the endpoint reserve bounds the two-zero expression, with both endpoint equalities. -/
def twoZeroEndpointLemma : Prop :=
  ∀ a g : ℝ, 0 < a → 0 < g →
    (∀ x : ℝ, 0 ≤ x → x ≤ g →
      twoZeroExpression a g x ≥ endpointReserve a g) ∧
    twoZeroExpression a g 0 = endpointReserve a g ∧
    twoZeroExpression a g g = endpointReserve a g

/-- Claim 11336: both partial derivatives of the endpoint reserve and their signs. -/
def endpointReserveDerivative : Prop :=
  ∀ a g : ℝ, 0 < a → 0 < g →
    HasDerivAt (fun a' : ℝ => endpointReserve a' g)
      (-4 * a * (a ^ 2 + 2 * g ^ 2) / (a ^ 2 + g ^ 2) ^ 3) a ∧
    HasDerivAt (fun g' : ℝ => endpointReserve a g')
      (-2 * g * (a ^ 2 + 3 * g ^ 2) / (a ^ 2 + g ^ 2) ^ 3) g ∧
    (-4 * a * (a ^ 2 + 2 * g ^ 2) / (a ^ 2 + g ^ 2) ^ 3) < 0 ∧
    (-2 * g * (a ^ 2 + 3 * g ^ 2) / (a ^ 2 + g ^ 2) ^ 3) < 0

/-- The main term and error term in the HSW count estimate. -/
def hswMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))

def hswErrorTerm (T : ℝ) : ℝ :=
  0.1038 * Real.log T + 0.2573 * Real.log (Real.log T) + 9.3675

def hswLeftLowerBound (T : ℝ) : ℝ :=
  hswMainTerm T - hswErrorTerm T -
    (hswMainTerm (4 * T / 5) + hswErrorTerm (4 * T / 5))

def hswRightLowerBound (T : ℝ) : ℝ :=
  hswMainTerm (6 * T / 5) - hswErrorTerm (6 * T / 5) -
    (hswMainTerm T + hswErrorTerm T)

/-- Claim 11342: both induced one-sided HSW lower bounds are positive and increasing from 200 onward. -/
def hswOneSidedCountBounds : Prop :=
  ∀ N : ℝ → ℝ,
    (∀ T : ℝ, Real.exp 1 ≤ T →
      |N T - hswMainTerm T| ≤ hswErrorTerm T) →
    hswLeftLowerBound 200 > 0 ∧ hswRightLowerBound 200 > 0 ∧
      (∀ T : ℝ, 200 ≤ T →
        0 < deriv hswLeftLowerBound T ∧
        0 < deriv hswRightLowerBound T ∧
        0 < hswLeftLowerBound T ∧
        0 < hswRightLowerBound T)

/-- The real sech power used by the Laplace and Hankel claims. -/
def realSechPower (p t : ℝ) : ℝ :=
  Real.rpow (1 / Real.cosh t) p

/-- Claim 11508: the bilateral Laplace transform of a positive real sech power. -/
def sechLaplaceTransform : Prop :=
  ∀ p : ℝ, 0 < p → ∀ s : ℂ, |s.re| < p →
    (∫ t : ℝ,
      Complex.exp (s * (t : ℂ)) * (realSechPower p t : ℂ)) =
      Complex.ofReal (Real.rpow 2 (p - 1)) *
        Complex.Gamma (((p : ℂ) + s) / 2) *
        Complex.Gamma (((p : ℂ) - s) / 2) / Complex.Gamma (p : ℂ)

/-- The oriented Hankel determinant for the sech power. -/
def orientedSechHankel (p : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      iteratedDeriv (i.val + j.val) (realSechPower p) t)

/-- The exponent in the all-order sech Hankel flag. -/
def sechHankelExponent (p : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * (p + (m : ℝ) - 1)

/-- A rising factorial over the reals. -/
def realRisingFactorial (p : ℝ) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range j, (p + (k : ℝ))

/-- The positive constant in the all-order sech Hankel flag. -/
def sechHankelConstant (p : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m,
    (j.factorial : ℝ) * realRisingFactorial p j

/-- Claim 11510: the exact all-order oriented Hankel flag for sech^p. -/
def sechHankelFlag : Prop :=
  ∀ p : ℝ, 0 < p → ∀ m : ℕ, ∀ t : ℝ,
    orientedSechHankel p m t =
      sechHankelConstant p m *
        Real.rpow (1 / Real.cosh t) (sechHankelExponent p m) ∧
    0 < sechHankelConstant p m

/-- Claim 11511: the contiguous Toda/Jacobi identity and the resulting recurrences. -/
def sechHankelTodaIdentity : Prop :=
  ∀ p : ℝ, 0 < p →
    (∀ t : ℝ, orientedSechHankel p 0 t = 1) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
      (iteratedDeriv 1 (orientedSechHankel p m)) t ^ 2 -
          orientedSechHankel p m t *
            (iteratedDeriv 2 (orientedSechHankel p m)) t =
        orientedSechHankel p (m - 1) t * orientedSechHankel p (m + 1) t) ∧
    (∀ m : ℕ, 1 ≤ m →
      sechHankelExponent p (m - 1) + sechHankelExponent p (m + 1) =
        2 * sechHankelExponent p m + 2 ∧
      sechHankelConstant p (m + 1) =
        sechHankelExponent p m * sechHankelConstant p m ^ 2 /
          sechHankelConstant p (m - 1))

/-- Claim 11519: the positive Euler-product coefficients in the real Dirichlet expansion. -/
def primeEulerCoefficient (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)

def primeEulerTerm (x : ℝ) (n : ℕ) : ℂ :=
  if 1 ≤ n then
    Complex.ofReal (primeEulerCoefficient n * Real.rpow (n : ℝ) (-x - 1 / 2))
  else 0

def positiveDirichletEulerRatio : Prop :=
  (∀ n : ℕ, 1 ≤ n → 0 < primeEulerCoefficient n) ∧
  (∀ x : ℝ, 1 / 2 < x →
    riemannZeta ((x + 1 / 2 : ℝ) : ℂ) /
        riemannZeta ((x + 5 / 2 : ℝ) : ℂ) =
      ∑' n : ℕ, primeEulerTerm x n)

/-- The associated Laguerre polynomial with parameter -1, written explicitly. -/
def realLaguerreMinusOne (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 1 else
    ∑ k ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ k * (Nat.choose (j - 1) (j - k) : ℝ) * x ^ k /
        (k.factorial : ℝ)

def taylorCoefficientAtZero (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  iteratedDeriv j f 0 / (j.factorial : ℝ)

def primeTwoGeneratingFunction (C₂ : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  C₂ * Real.exp (-Real.log 2 * (r : ℝ) * (1 - s) / (1 + s))

/-- Claim 11550: the exact prime-two associated-Laguerre coefficient formula. -/
def primeTwoLaguerreCoefficient : Prop :=
  ∀ r j : ℕ,
    taylorCoefficientAtZero
        (fun s : ℝ => Real.exp (-Real.log 2 * (r : ℝ) * (1 - s) / (1 + s))) j =
      Real.exp (-Real.log 2 * (r : ℝ)) * (-1 : ℝ) ^ j *
        realLaguerreMinusOne j (2 * Real.log 2 * (r : ℝ)) ∧
    (∀ C₂ : ℝ,
      taylorCoefficientAtZero (primeTwoGeneratingFunction C₂ r) j =
        C₂ * Real.exp (-Real.log 2 * (r : ℝ)) * (-1 : ℝ) ^ j *
          realLaguerreMinusOne j (2 * Real.log 2 * (r : ℝ)))

/-- Claim 11527: a real two-step ratio together with the complete limiting normalization is unique. -/
def twoStepStirlingUniqueness : Prop :=
  ∀ X Y : ℝ → ℝ,
    (∀ x : ℝ, X x ≠ 0 ∧ Y x ≠ 0) →
    (∀ x : ℝ, Y (x + 2) / Y x = X (x + 2) / X x) →
    Filter.Tendsto (fun x : ℝ => Y x / X x) Filter.atTop (nhds 1) →
    ∀ x : ℝ, Y x = X x

/-- The finite product in the two-step reconstruction formula. -/
def twoStepReconstructionTerm (X : ℝ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  X (x + 2 * (N : ℝ)) /
    ∏ k ∈ Finset.range N,
      (X (x + 2 * (k : ℝ) + 2) / X (x + 2 * (k : ℝ)))

/-- Claim 11528: the normalized product is a telescoping reconstruction. -/
def twoStepTelescopingReconstruction : Prop :=
  ∀ X : ℝ → ℝ, (∀ x : ℝ, X x ≠ 0) → ∀ x : ℝ,
    (∀ N : ℕ, twoStepReconstructionTerm X x N = X x) ∧
    Filter.Tendsto (twoStepReconstructionTerm X x) Filter.atTop (nhds (X x))

/-- The polynomial p(z)=z(z-1) in the divisor-coded transfer model. -/
def divisorModelPolynomial : Polynomial ℂ :=
  Polynomial.X * (Polynomial.X - 1)

def divisorModelTransfer (f : Polynomial ℂ) (z : ℂ) : ℂ :=
  divisorModelPolynomial.eval z /
      divisorModelPolynomial.eval (z - 2 * Complex.I) *
    f.eval (z - 2 * Complex.I)

/-- Polynomiality of a rational transfer, expressed on its natural denominator domain. -/
def isPolynomialOnDivisorDomain (F : ℂ → ℂ) : Prop :=
  ∃ q : Polynomial ℂ, ∀ z : ℂ,
    divisorModelPolynomial.eval (z - 2 * Complex.I) ≠ 0 → q.eval z = F z

/-- Claim 11531: polynomial output is equivalent to divisibility by p, with cancellation on the ideal. -/
def polynomialDivisorTransfer : Prop :=
  (∀ f : Polynomial ℂ,
    isPolynomialOnDivisorDomain (divisorModelTransfer f) ↔
      divisorModelPolynomial ∣ f) ∧
  (∀ g : Polynomial ℂ, ∀ z : ℂ,
    divisorModelPolynomial.eval (z - 2 * Complex.I) ≠ 0 →
      divisorModelTransfer (divisorModelPolynomial * g) z =
        divisorModelPolynomial.eval z * g.eval (z - 2 * Complex.I))

/-- Claim 11570: a continuous complex finite-dimensional representation of a profinite group has finite image. -/
def profiniteComplexRepresentationFiniteImage : Prop :=
  ∀ (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [T2Space Γ] [TotallyDisconnectedSpace Γ] [IsTopologicalGroup Γ]
    (n : ℕ) (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) ℂ),
    Continuous ρ → Set.Finite (Set.range ρ)

/-- The two scalar/Jordan matrices used to exhibit determinant loss. -/
def scalarJordanMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z, 0; 0, z]

def nontrivialJordanMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z, 1; 0, z]

def zeroNilpotentMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 0]

def nonzeroNilpotentMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- Claim 11583: equal completed determinants do not determine the Jordan module. -/
def determinantLosesJordanStructure : Prop :=
  (∀ z : ℂ,
    Matrix.det (scalarJordanMatrix z) = z ^ 2 ∧
      Matrix.det (nontrivialJordanMatrix z) = z ^ 2) ∧
  ¬ ∃ P Q : Matrix (Fin 2) (Fin 2) ℂ,
    P * Q = 1 ∧ Q * P = 1 ∧
      P * zeroNilpotentMatrix * Q = nonzeroNilpotentMatrix

end MathlibPlus.Open.ResearchFormalization
