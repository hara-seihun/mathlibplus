import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1077Claim28666

abbrev K3 := ZMod 3
abbrev X3 := K3 × K3
abbrev V3 (m : ℕ) := Fin m → K3

def e₁ : X3 :=
  (1, 0)

def e₂ : X3 :=
  (0, 1)

def d : X3 :=
  e₁ + e₂

def h : X3 :=
  e₁ - e₂

def oddMap {m : ℕ} (f : X3 → V3 m) : Prop :=
  ∀ x : X3, f (-x) = -f x

def normalizedSecondDerivative {m : ℕ} (f : X3 → V3 m)
    (a c x : X3) : V3 m :=
  (f (x + c + a) - f (x + c)) - (f (c + a) - f c)

def correctedMap {m : ℕ} (f : X3 → V3 m)
    (ℓ : X3 →ₗ[K3] V3 m) : X3 → V3 m :=
  fun x => f x + ℓ x

/-- Claim 28666: a linear correction removes the four axis defects, leaves
only the two diagonal defect values, and preserves every normalized second
derivative. -/
def claim28666 : Prop :=
  ∀ (m : ℕ) (f : X3 → V3 m), oddMap f →
    ∃ ℓ : X3 →ₗ[K3] V3 m,
      ℓ e₁ = -f e₁ ∧
      ℓ e₂ = -f e₂ ∧
      let g := correctedMap f ℓ
      ∃ A B : V3 m,
        A = g d ∧ B = g h ∧
        g 0 = 0 ∧
        g e₁ = 0 ∧
        g (-e₁) = 0 ∧
        g e₂ = 0 ∧
        g (-e₂) = 0 ∧
        g (-d) = -A ∧
        g (-h) = -B ∧
        (∀ x : X3,
          g x = 0 ∨ g x = A ∨ g x = -A ∨ g x = B ∨ g x = -B) ∧
        (∀ a c x : X3,
          normalizedSecondDerivative g a c x =
            normalizedSecondDerivative f a c x)

end MathlibPlus.Open.ResearchFormalization.R1077Claim28666
