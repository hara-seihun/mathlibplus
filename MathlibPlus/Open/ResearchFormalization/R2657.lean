import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2657

noncomputable section

def positiveCoefficientCone : Set (Polynomial ℤ) :=
  {p | ∀ d, 0 ≤ p.coeff d}

def isPositiveCone {R : Type*} [CommRing R] (C : Set R) : Prop :=
  0 ∈ C ∧ 1 ∈ C ∧
    (∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) ∧
    (∀ a ∈ C, ∀ b ∈ C, a * b ∈ C)

def everyMinorInCone {R : Type*} [CommRing R]
    {m n : ℕ} (C : Set R) (M : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (e : Fin k ↪ Fin m) (f : Fin k ↪ Fin n),
    Matrix.det (M.submatrix e f) ∈ C

/-- Total nonnegativity relative to an explicitly given positive cone. -/
def positiveConeTotalNonnegativity {R : Type*} [CommRing R]
    {m n : ℕ} (C : Set R) (M : Matrix (Fin m) (Fin n) R) : Prop :=
  isPositiveCone C ∧ everyMinorInCone C M

def polynomialPositiveConeTotalNonnegativity {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Polynomial ℤ)) : Prop :=
  positiveConeTotalNonnegativity positiveCoefficientCone M

end

end MathlibPlus.Open.ResearchFormalization.R2657
