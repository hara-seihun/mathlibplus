import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim28870

abbrev Ternary := ZMod 3
abbrev Plane := Fin 2 → Ternary

def e₁ : Plane := fun i => if i = 0 then 1 else 0

def e₂ : Plane := fun i => if i = 1 then 1 else 0

def normalizedMap {V : Type*} [AddCommGroup V] [Module Ternary V]
    (g : Plane → V) : Prop :=
  (∀ x, g (-x) = -g x) ∧
    (∀ t : Ternary, g (t • e₁) = 0 ∧ g (t • e₂) = 0)

def normalizedDerivative {V : Type*} [AddCommGroup V] [Module Ternary V]
    (g : Plane → V) (a c x : Plane) : V :=
  (g (x + c + a) - g (x + c)) - (g (c + a) - g c)

/-- Claim 28870: the four nonzero sign representatives have the exact
    derivative pairs listed in the admitted statement. -/
def explicitDerivativeWitnesses_claim28870 : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module Ternary V]
    [FiniteDimensional Ternary V],
    ∀ g : Plane → V, normalizedMap g →
      let A := g (e₁ + e₂)
      let B := g (e₁ - e₂)
      normalizedDerivative g e₂ 0 e₁ = A ∧
        normalizedDerivative g e₂ (-e₁) e₁ = B ∧
        normalizedDerivative g e₁ 0 e₂ = A ∧
        normalizedDerivative g e₁ (-e₁) e₂ = B ∧
        normalizedDerivative g e₂ (-e₂) (e₁ + e₂) = A ∧
        normalizedDerivative g e₂ (-e₁) (e₁ + e₂) = B ∧
        normalizedDerivative g e₂ e₂ (e₁ - e₂) = A ∧
        normalizedDerivative g e₂ (-e₁) (e₁ - e₂) = B

end MathlibPlus.Open.ResearchFormalization.Claim28870
