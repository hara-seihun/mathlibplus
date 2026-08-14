import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The exact quadratic source profile from Claim 3089. -/
def freshQuadraticSourceProfile (P₀ : Polynomial ℚ) : Prop :=
  ∀ u : ℚ,
    Polynomial.eval u P₀ =
      1 - (0.8824739608624199 : ℚ) * u +
        (2.816598275979663 : ℚ) * u ^ 2

abbrev V := Fin 3 → ZMod 3
abbrev G := ZMod 4 × V

def inverseClosed (A : Set G) : Prop :=
  ∀ x, x ∈ A → -x ∈ A

def reflectedConnectionSet (S : Set G) : Set G :=
  {x | (-x.1, x.2) ∈ S}

def fiberPermutation (σ : V → Equiv.Perm (ZMod 4)) : G → G :=
  fun x => (σ x.2 x.1, x.2)

def CayleyRelation (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

def fiberPreservingCayleyIsomorphism
    (S T : Set G) (σ : V → Equiv.Perm (ZMod 4)) : Prop :=
  Function.Bijective (fiberPermutation σ) ∧
    ∀ x y : G,
      CayleyRelation S x y ↔
        CayleyRelation T (fiberPermutation σ x) (fiberPermutation σ y)

def fiberDifferenceCondition
    (S T : Set G) (σ : V → Equiv.Perm (ZMod 4)) : Prop :=
  ∀ (a c : ZMod 4) (v w : V),
    (a, w) ∈ S ↔
      (σ (v + w) (c + a) - σ v c, w) ∈ T

/-- Claim 59734: fiber permutations cannot produce a new connection set,
except for the inversion of the cyclic coordinate; the Cayley-isomorphism
formulation is included as its stated consequence. -/
def ciMixedAbelianResidualFiberPermutationRigidity : Prop :=
  (∀ (S T : Set G) (σ : V → Equiv.Perm (ZMod 4)),
    inverseClosed S →
    inverseClosed T →
    fiberDifferenceCondition S T σ →
    T = S ∨ T = reflectedConnectionSet S) ∧
  (∀ (S T : Set G) (σ : V → Equiv.Perm (ZMod 4)),
    inverseClosed S →
    inverseClosed T →
    fiberPreservingCayleyIsomorphism S T σ →
    ∃ e : G ≃+ G, e '' S = T)

end MathlibPlus.Open.ResearchFormalization
