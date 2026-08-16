import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankel15112

noncomputable section

/-- Iterated differentiation used by normalized Hermite jets. -/
def iteratedPolynomialDerivative : ℕ → Polynomial ℂ → Polynomial ℂ
  | 0, p => p
  | k + 1, p => iteratedPolynomialDerivative k (Polynomial.derivative p)

/-- The finite sigma type indexing every normalized derivative jet through the
specified multiplicity at every displayed root. -/
abbrev jetIndex {J : ℕ} (mu : Fin J → ℕ) :=
  Σ j : Fin J, Fin (mu j)

/-- The normalized Hermite jet of a polynomial. -/
def normalizedHermiteJet {J : ℕ}
    (zeta : Fin J → ℂ) (mu : Fin J → ℕ)
    (p : Polynomial ℂ) (jk : jetIndex mu) : ℂ :=
  Polynomial.eval (zeta jk.1)
    (iteratedPolynomialDerivative jk.2.val p) /
      (Nat.factorial jk.2.val : ℂ)

/-- The full jet vector J_S(p). -/
def normalizedHermiteJets {J : ℕ}
    (zeta : Fin J → ℂ) (mu : Fin J → ℕ)
    (p : Polynomial ℂ) : jetIndex mu → ℂ :=
  normalizedHermiteJet zeta mu p

/-- The confluent Hermite evaluation matrix in the monomial basis. -/
def confluentHermiteMatrix {J : ℕ}
    (zeta : Fin J → ℂ) (mu : Fin J → ℕ) :
    Matrix (jetIndex mu) (Fin (∑ j : Fin J, mu j)) ℂ :=
  fun row n =>
    if row.2.val ≤ n.val then
      (Nat.choose n.val row.2.val : ℂ) *
        zeta row.1 ^ (n.val - row.2.val)
    else 0

/-- The coefficient vector of a remainder in the degree-bounded monomial
carrier. -/
def polynomialCoefficientVector (m : ℕ) (p : Polynomial ℂ) : Fin m → ℂ :=
  fun n => p.coeff n.val

/-- Euclidean two-norm on a finite complex coordinate carrier. -/
def euclideanTwoNorm {ι : Type*} [Fintype ι]
    (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The set of values of a finite matrix on unit Euclidean vectors. -/
def unitImageNorms {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : Set ℝ :=
  {s : ℝ | ∃ v : κ → ℂ,
    euclideanTwoNorm v = 1 ∧
      s = euclideanTwoNorm (M.mulVec v)}

/-- The variational smallest singular value of a finite complex matrix. -/
noncomputable def smallestSingularValue {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : ℝ :=
  sInf (unitImageNorms M)

/-- The variational largest singular value of a finite complex matrix. -/
noncomputable def largestSingularValue {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : ℝ :=
  sSup (unitImageNorms M)

/-- Claim 15112: for a polynomial remainder R=P mod S, the normalized
Hermite jets agree, and their Euclidean norm is bounded above and below by the
actual smallest and largest singular values of the explicit confluent
Hermite matrix applied to the coefficient vector of R. -/
def claim_15112 : Prop :=
  ∀ (J : ℕ) (zeta : Fin J → ℂ) (mu : Fin J → ℕ)
    (P S R : Polynomial ℂ),
    (∀ u v : Fin J, u ≠ v → zeta u ≠ zeta v) →
      (∀ u : Fin J, 0 < mu u) →
        S = ∏ u : Fin J,
          (Polynomial.X - Polynomial.C (zeta u)) ^ mu u →
          R = P % S →
            let m := ∑ u : Fin J, mu u
            let Phi := confluentHermiteMatrix zeta mu
            normalizedHermiteJets zeta mu P =
                normalizedHermiteJets zeta mu R ∧
              smallestSingularValue Phi *
                    euclideanTwoNorm (polynomialCoefficientVector m R) ≤
                euclideanTwoNorm (normalizedHermiteJets zeta mu P) ∧
              euclideanTwoNorm (normalizedHermiteJets zeta mu P) ≤
                largestSingularValue Phi *
                    euclideanTwoNorm (polynomialCoefficientVector m R)

end

end MathlibPlus.Open.NewResearch2.RationalHankel15112
