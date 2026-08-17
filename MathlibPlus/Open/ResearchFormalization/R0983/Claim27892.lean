import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a001b7_8151_7192_bf7c_77d39208c988

namespace MathlibPlus.Open.ResearchFormalization.R0983

open MathlibPlus.Open.ResearchFormalizationBatch_01a001b7_8151_7192_bf7c_77d39208c988

/-- The additive derivative word `d_{f,g}(c) = f(c+g) - f(g)`. -/
def additiveDerivativeWord
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A × B → A × B) (g c : A × B) : A × B :=
  f (c + g) - f g

/-- The normalized additive relative derivative `f⁻¹ ∘ d_{f,g}` for the
explicit identity-base fibre map and its coordinatewise inverse. -/
def normalizedIdentityBaseRelativeDerivative
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (g c : A × B) : A × B :=
  (fun ab => (ab.1, (p ab.1).symm ab.2))
    (additiveDerivativeWord
      (normalizedIdentityBaseFiberMap A B p) g c)

/-- Restriction of the normalized relative derivative indexed by `(u,t)` to
 the fibre whose first coordinate is `a`. -/
def derivativeFiberRestriction
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (u : A) (t : B) (a : A) : B → B :=
  fun x =>
    (normalizedIdentityBaseRelativeDerivative p (u, t) (a, x)).2

/-- The displayed formula for the restriction to the `a`-fibre. -/
def displayedFiberDerivative
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (u : A) (t : B) (a : A) : B → B :=
  fun x => (p a).symm (p (a + u) (x + t) - p u t)

/-- Claim 27892: the normalized relative derivative of the admitted
identity-base fibre map has the displayed restriction on every `a`-fibre. -/
def fiberRestrictionOfDerivative_claim27892 : Prop :=
  ∀ (A B : Type*) [Fintype A] [AddCommGroup A]
    [Fintype B] [AddCommGroup B]
    (_elementaryTwo : ∀ a : A, a + a = 0)
    (_oddOrder : Odd (Fintype.card B))
    (p : A → Equiv.Perm B)
    (_normalized : p 0 = Equiv.refl B),
    ∀ (u : A) (t : B) (a : A),
      derivativeFiberRestriction p u t a =
        displayedFiberDerivative p u t a

end MathlibPlus.Open.ResearchFormalization.R0983
