import Mathlib

noncomputable section

namespace MathlibPlus
namespace Open
namespace FormalizationBatch

/-- The one-sided Hardy tail occurring in the admitted jet statement. -/
def hardyTail (f : ℝ → ℂ) (U : ℝ) : ℂ → ℂ :=
  fun z => ∫ u : ℝ in Set.Ioi U, Complex.exp (z * (u : ℂ)) * f u

/-- The reciprocal Tate square factor occurring in the admitted jet statement. -/
def hardySquareFactor : ℂ → ℂ :=
  fun z => (riemannZeta (1 + 2 * z))⁻¹

/-- The value/first-jet matrix and its invertibility are part of the exact claim. -/
def jet_determinant_invertibility : Prop :=
  ∀ (f : ℝ → ℂ) (U : ℝ) (G : ℂ → ℂ),
    let H := hardyTail f U
    let M := hardySquareFactor
    (∀ z : ℂ, G z = M z * H z) →
      (∀ z : ℂ,
          Matrix.det (!![M z, 0; deriv M z, M z] : Matrix (Fin 2) (Fin 2) ℂ) = M z ^ 2) ∧
      (∀ z : ℂ, M z ≠ 0 →
        Function.Bijective
          (fun p : ℂ × ℂ =>
            (M z * p.1, deriv M z * p.1 + M z * p.2))) ∧
      (∀ ω : ℝ, 0 < ω → ω < (1 / 2 : ℝ) →
        M (ω : ℂ) ≠ 0 ∧ M (-(ω : ℂ)) ≠ 0) ∧
      (∀ z : ℂ,
        M z ≠ 0 → DifferentiableAt ℂ M z → DifferentiableAt ℂ H z →
          DifferentiableAt ℂ G z →
            H z = G z / M z ∧
            deriv H z = deriv G z / M z - deriv M z * G z / M z ^ 2)

/-- Orthogonal projection, written on the bounded-operator carrier. -/
def IsOrthogonalProjection {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (P : H →L[ℂ] H) : Prop :=
  (∀ x : H, P (P x) = P x) ∧
    (∀ x y : H, @inner ℂ H _ (P x) y = @inner ℂ H _ x (P y))

/-- Self-adjointness, written on the bounded-operator carrier. -/
def IsSelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H) : Prop :=
  ∀ x y : H, @inner ℂ H _ (T x) y = @inner ℂ H _ x (T y)

/-- The Hermitian first-order cutoff current i[P,T]. -/
def cutoffCurrent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (P T : H →L[ℂ] H) : H →L[ℂ] H :=
  Complex.I • (P.comp T - T.comp P)

/-- Positivity and negativity of a self-adjoint bounded operator. -/
def PositiveSemidefinite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : H →L[ℂ] H) : Prop :=
  ∀ x : H, 0 ≤ (@inner ℂ H _ x (S x)).re

def NegativeSemidefinite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : H →L[ℂ] H) : Prop :=
  ∀ x : H, (@inner ℂ H _ x (S x)).re ≤ 0

/-- Vanishing of both off-diagonal blocks relative to P H ⊕ (I-P) H. -/
def CrossingBlockZero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (P T : H →L[ℂ] H) : Prop :=
  ∀ x : H,
    P (T (x - P x)) = 0 ∧
      T (P x) - P (T (P x)) = 0

/-- Vanishing of the cutoff commutator. -/
def CutoffCommutes {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (P T : H →L[ℂ] H) : Prop :=
  ∀ x : H, P (T x) = T (P x)

/-- The semidefinite current characterization on a complex Hilbert space. -/
def semidefinite_current_iff_cutoff_commutes : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P T : H →L[ℂ] H),
    IsOrthogonalProjection P → IsSelfAdjoint T →
      let J := cutoffCurrent P T
      (PositiveSemidefinite J ∨ NegativeSemidefinite J ↔ CrossingBlockZero P T) ∧
        (CrossingBlockZero P T ↔ CutoffCommutes P T) ∧
        (CrossingBlockZero P T → J = 0 ∧ PositiveSemidefinite J ∧ NegativeSemidefinite J) ∧
        (J ≠ 0 → ¬ PositiveSemidefinite J ∧ ¬ NegativeSemidefinite J)

/-- Each nonzero eigenline has zero expectation for the cutoff current. -/
def eigenvector_current_expectation_vanishes : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P T : H →L[ℂ] H),
    IsOrthogonalProjection P → IsSelfAdjoint T →
      ∀ (ψ : H) (eigenvalue : ℂ), ψ ≠ 0 → T ψ = eigenvalue • ψ →
        @inner ℂ H _ ψ (cutoffCurrent P T ψ) = 0

/-- The divisor-count coefficient fixture τ₀(n)=d(n). -/
def divisorCount (n : ℕ) : ℕ := (Nat.divisors n).card

def tauZero (n : ℕ) : ℕ := divisorCount n

def crossPrimeBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![tauZero 2, tauZero 3; tauZero 6, tauZero 4]

/-- The four-dimensional current [[0,iB],[-iB*,0]] for B=[[2,2],[4,3]]. -/
def crossPrimeCurrent : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, Complex.I * crossPrimeBlock 0 0, Complex.I * crossPrimeBlock 0 1;
     0, 0, Complex.I * crossPrimeBlock 1 0, Complex.I * crossPrimeBlock 1 1;
     -(Complex.I * crossPrimeBlock 0 0), -(Complex.I * crossPrimeBlock 1 0), 0, 0;
     -(Complex.I * crossPrimeBlock 0 1), -(Complex.I * crossPrimeBlock 1 1), 0, 0]

def MatrixHasEigenvalue (J : Matrix (Fin 4) (Fin 4) ℂ) (eigenvalue : ℂ) : Prop :=
  ∃ v : Fin 4 → ℂ, v ≠ 0 ∧ J.mulVec v = eigenvalue • v

/-- The two positive singular-value roots in the admitted witness. -/
def crossPrimePositive : ℝ := Real.sqrt ((33 + Real.sqrt 1073) / 2)
def crossPrimeNegative : ℝ := Real.sqrt ((33 - Real.sqrt 1073) / 2)

/-- A constrained eigenbasis formulation of exact inertia (2,2,0). -/
def HasInertiaTwoTwoZero (J : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ e : Fin 4 → (Fin 4 → ℂ),
    (∀ v : Fin 4 → ℂ, ∃ c : Fin 4 → ℂ, ∑ i, c i • e i = v) ∧
    (∀ i : Fin 4, e i ≠ 0) ∧
    J.mulVec (e 0) = (crossPrimePositive : ℂ) • e 0 ∧
    J.mulVec (e 1) = (-(crossPrimePositive : ℂ)) • e 1 ∧
    J.mulVec (e 2) = (crossPrimeNegative : ℂ) • e 2 ∧
    J.mulVec (e 3) = (-(crossPrimeNegative : ℂ)) • e 3 ∧
    0 < crossPrimePositive ∧ 0 < crossPrimeNegative

/-- The exact finite cross-prime current witness. -/
def exact_cross_prime_current_witness : Prop :=
  crossPrimeBlock = !![2, 2; 4, 3] ∧
    tauZero 2 = 2 ∧ tauZero 3 = 2 ∧ tauZero 6 = 4 ∧ tauZero 4 = 3 ∧
    Matrix.charpoly crossPrimeCurrent =
      Polynomial.X ^ 4 - Polynomial.C (33 : ℂ) * Polynomial.X ^ 2 + Polynomial.C (4 : ℂ) ∧
    (∀ eigenvalue : ℂ,
      MatrixHasEigenvalue crossPrimeCurrent eigenvalue ↔
        eigenvalue = (crossPrimePositive : ℂ) ∨
        eigenvalue = -(crossPrimePositive : ℂ) ∨
        eigenvalue = (crossPrimeNegative : ℂ) ∨
        eigenvalue = -(crossPrimeNegative : ℂ)) ∧
    HasInertiaTwoTwoZero crossPrimeCurrent

end FormalizationBatch
end Open
end MathlibPlus
