import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatchCoupling

/-- Prime weights, viewed as real scalar weights when needed. -/
def realPrimeWeight (x : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x = (p : ℝ)

/-- The two-sector matrix with its two directed cross-sector couplings. -/
def twoSectorCouplingMatrix (x y : ℕ) (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), a; b, (y : ℂ)]

def twoSectorCouplingModel (x y : ℕ) (a b : ℂ)
    (hx : Nat.Prime x) (hy : Nat.Prime y) (hxy : x ≠ y) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  twoSectorCouplingMatrix x y a b

/-- A triangular cross-prime coupling has the diagonal characteristic data. -/
def triangularCouplingSpectrallyInert : Prop :=
  ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q → ∀ a : ℂ,
    let T : Matrix (Fin 2) (Fin 2) ℂ := !![(p : ℂ), a; 0, (q : ℂ)]
    (∀ n : ℕ,
        Matrix.trace (T ^ n) = (p : ℂ) ^ n + (q : ℂ) ^ n) ∧
      Matrix.charpoly T =
        (Polynomial.X - Polynomial.C (p : ℂ)) *
          (Polynomial.X - Polynomial.C (q : ℂ)) ∧
      (∀ z : ℂ,
        Matrix.det (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - T) =
          (z - (p : ℂ)) * (z - (q : ℂ)))

end MathlibPlus.Open.ResearchBatchCoupling
