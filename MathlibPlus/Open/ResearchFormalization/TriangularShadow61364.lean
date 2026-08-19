import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.TriangularShadow61364

abbrev fibreA := (Fin 2 → ZMod 2) × ZMod 3

/-- An elementary-abelian Sylow subgroup, written for the additive carriers
used in the theorem. -/
def elementarySylow (p : ℕ) {B : Type*} [Fintype B]
    [AddCommGroup B] (P : Sylow p (Multiplicative B)) : Prop :=
  (∀ x y : P, x * y = y * x) ∧ ∀ x : P, x ^ p = 1

/-- The exact finite-abelian hypothesis on the two specified Sylow parts. -/
def elementaryTwoThreeSylows (B : Type*) [Fintype B]
    [AddCommGroup B] : Prop :=
  (∀ P : Sylow 2 (Multiplicative B), elementarySylow 2 P) ∧
    ∀ P : Sylow 3 (Multiplicative B), elementarySylow 3 P

/-- The displacement subgroup appearing in the period interpolation. -/
def triangularPeriodSubgroup {B : Type*} [AddCommGroup B]
    (t : B → fibreA) (b : B) : AddSubgroup fibreA :=
  AddSubgroup.closure
    (Set.range (fun x : B => t b + t x - t (x + b)))

/-- The arbitrary pointed triangular shear. -/
def triangularShear {B : Type*} [AddCommGroup B]
    (t : B → fibreA) : fibreA × B → fibreA × B :=
  fun p => (p.1 + t p.2, p.2)

/-- The group-automorphism shadow associated with an additive homomorphism. -/
def linearTriangularMap {B : Type*} [AddCommGroup B]
    (ell : B →+ fibreA) : fibreA × B → fibreA × B :=
  fun p => (p.1 + ell p.2, p.2)

/-- Identity-free connection sets on the direct-product group. -/
def identityFree {B : Type*} [AddCommGroup B]
    (S : Set (fibreA × B)) : Prop :=
  S ⊆ (Set.univ : Set (fibreA × B)) \ {0}

/-- Directed Cayley adjacency in additive notation. -/
def directedCayleyAdj {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

/-- A specified bijection as an isomorphism of directed Cayley relations. -/
def directedCayleyIsomorphism {G : Type*} [AddGroup G]
    (q : G → G) (S T : Set G) : Prop :=
  Function.Bijective q ∧
    ∀ x y, directedCayleyAdj S x y ↔ directedCayleyAdj T (q x) (q y)

/-- The simultaneous directed-Cayley premise for a finite labelled family. -/
def familyCarriedByShear {B I : Type*} [Fintype I]
    [AddCommGroup B] (t : B → fibreA)
    (S T : I → Set (fibreA × B)) : Prop :=
  ∀ i,
    identityFree (S i) ∧
      identityFree (T i) ∧
        directedCayleyIsomorphism (triangularShear t) (S i) (T i)

/-- The common group-automorphism shadow for the whole family. -/
def linearShadowFamily {B I : Type*} [Fintype I]
    [AddCommGroup B] (ell : B →+ fibreA)
    (S T : I → Set (fibreA × B)) : Prop :=
  ∃ alpha : (fibreA × B) ≃+ (fibreA × B),
    (∀ p, alpha p = linearTriangularMap ell p) ∧
      ∀ i, alpha '' (S i) = T i

/-- Claim 61364: period interpolation and the one simultaneous
triangular group-automorphism shadow for every finite family of directed
Cayley relations. -/
def claim61364 : Prop :=
  ∀ (B : Type*) [Fintype B] [AddCommGroup B],
    elementaryTwoThreeSylows B →
      ∀ (t : B → fibreA),
        t 0 = 0 →
          ∃ ell : B →+ fibreA,
            (∀ b, t b - ell b ∈ triangularPeriodSubgroup t b) ∧
              ∀ (I : Type*) [Fintype I]
                (S T : I → Set (fibreA × B)),
                familyCarriedByShear t S T →
                  linearShadowFamily ell S T

end MathlibPlus.Open.ResearchFormalization.TriangularShadow61364
