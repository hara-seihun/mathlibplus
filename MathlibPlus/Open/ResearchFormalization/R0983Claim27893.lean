import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0983

noncomputable section

/-- The normalized identity-base fiber map. -/
def fiberMap27893
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) : Equiv.Perm (A × B) :=
  Equiv.prodCongrRight p

/-- The normalized relative derivative `f⁻¹ ∘ d_{f,g}` on an additive group. -/
def normalizedRelativeDerivative27893
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (g x : G) : G :=
  f.symm (f (x + g) - f g)

/-- Restriction to the `a`-fiber of the derivative indexed by `(u,t)`. -/
def derivativeRestriction27893
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (a u : A) (t x : B) : B :=
  (normalizedRelativeDerivative27893 (fiberMap27893 p)
      (u, t) (a, x)).2

/-- The explicit fiber formula supplied from the derivative restriction. -/
def fiberDerivativeFormula27893
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (a u : A) (t x : B) : B :=
  (p a).symm (p (a + u) (x + t) - p u t)

/-- The first special family `p⁻¹ τ_{-t} p τ_t`. -/
def specialR27893
    {B : Type*} [AddCommGroup B]
    (p : Equiv.Perm B) (t x : B) : B :=
  p.symm (p (x + t) - t)

/-- The second special family `p⁻¹ τ_{t-p(t)}`. -/
def specialQ27893
    {B : Type*} [AddCommGroup B]
    (p : Equiv.Perm B) (t x : B) : B :=
  p.symm (x + t - p t)

/-- Claim 27893: the general derivative restricts to the displayed formula,
and the exponent-two specializations give the two explicit families. -/
def claim27893 : Prop :=
  ∀ (A B : Type*) [Fintype A] [AddCommGroup A]
    [Fintype B] [AddCommGroup B],
    (∀ a : A, a + a = 0) →
    (∃ n : ℕ, Fintype.card B = 2 * n + 1) →
    ∀ p : A → Equiv.Perm B,
      p 0 = Equiv.refl B →
      (∀ a u : A, ∀ t x : B,
        derivativeRestriction27893 p a u t x =
          fiberDerivativeFormula27893 p a u t x) ∧
      (∀ a : A, ∀ t x : B,
        derivativeRestriction27893 p a 0 t x =
          specialR27893 (p a) t x) ∧
      (∀ a : A, ∀ t x : B,
        derivativeRestriction27893 p a a t x =
          specialQ27893 (p a) t x)

end
end MathlibPlus.Open.ResearchFormalization.R0983
