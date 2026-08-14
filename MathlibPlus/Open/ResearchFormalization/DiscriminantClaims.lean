import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.DiscriminantClaims

universe u

/-- The displayed collars, with the ellipses made precise by degree bounds. -/
def q0Collar {R : Type u} [Semiring R] (s : ℕ) (Q₀ : Polynomial R) : Prop :=
  Q₀.natDegree ≤ s + 2 ∧
    Q₀.coeff (s + 2) = 1 ∧ Q₀.coeff (s + 1) = 1 ∧ Q₀.coeff s = 1

def q1Collar {R : Type u} [Semiring R] (s : ℕ) (Q₁ : Polynomial R)
    (K M H : R) : Prop :=
  Q₁.natDegree ≤ s - 1 ∧
    Q₁.coeff (s - 1) = K ∧ Q₁.coeff (s - 2) = M ∧ Q₁.coeff (s - 3) = H

def q2Collar {R : Type u} [Semiring R] (s : ℕ) (Q₂ : Polynomial R)
    (A B C : R) : Prop :=
  Q₂.natDegree ≤ s - 4 ∧
    Q₂.coeff (s - 4) = A ∧ Q₂.coeff (s - 5) = B ∧ Q₂.coeff (s - 6) = C

def claim_40932 : Prop := by
  classical
  exact ∀ {R : Type u} [CommRing R] [Nontrivial R]
    (a b : ℕ) (Q₀ Q₁ Q₂ : Polynomial R)
    (K M H A B C : R),
    6 ≤ a + b →
    q0Collar (a + b) Q₀ →
    q1Collar (a + b) Q₁ K M H →
    q2Collar (a + b) Q₂ A B C →
    let Δ := Q₁ ^ 2 - 4 * Q₀ * Q₂
    let Λ := Δ.coeff (2 * (a + b) - 2)
    let twoN := Δ.coeff (2 * (a + b) - 3)
    let T := Δ.coeff (2 * (a + b) - 4)
    Λ = K ^ 2 - 4 * A ∧
      twoN = 2 * K * M - 4 * (A + B) ∧
      T = M ^ 2 + 2 * K * H - 4 * (A + B + C)

end MathlibPlus.Open.ResearchFormalization.DiscriminantClaims
