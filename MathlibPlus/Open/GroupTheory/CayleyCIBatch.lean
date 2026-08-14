import Mathlib

namespace MathlibPlus.Open.GroupTheory.CayleyCI

variable {R : Type*} [Group R] [Fintype R] [DecidableEq R]

def directedCayleyAdj (S : Set R) (x y : R) : Prop :=
  x⁻¹ * y ∈ S

def undirectedCayleyAdj (S : Set R) (x y : R) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

def inverseClosed (S : Set R) : Prop :=
  ∀ x, x ∈ S ↔ x⁻¹ ∈ S

/-- Isomorphism of two finite relational Cayley presentations. -/
def relationIsomorphism (adj₁ adj₂ : R → R → Prop) : Prop :=
  ∃ e : Equiv.Perm R, ∀ x y, adj₁ x y ↔ adj₂ (e x) (e y)

def connectionSetMappedByAutomorphism (S T : Set R) : Prop :=
  ∃ φ : R ≃* R, ∀ x, x ∈ S ↔ φ x ∈ T

def isDCI (S : Set R) : Prop :=
  ∀ T : Set R,
    relationIsomorphism (directedCayleyAdj S) (directedCayleyAdj T) →
      connectionSetMappedByAutomorphism S T

def isCI (S : Set R) : Prop :=
  ∀ T : Set R,
    relationIsomorphism (undirectedCayleyAdj S) (undirectedCayleyAdj T) →
      connectionSetMappedByAutomorphism S T

/-- A subgroup of permutations acts regularly on the underlying group. -/
def isRegularSubgroup (H : Subgroup (Equiv.Perm R)) : Prop :=
  ∀ x y : R, ∃! h : H, (h : Equiv.Perm R) x = y

def isRegularRSubgroup (adj : R → R → Prop)
    (H : Subgroup (Equiv.Perm R)) : Prop :=
  (∀ h : Equiv.Perm R, h ∈ H →
      ∀ x y, adj x y ↔ adj (h x) (h y)) ∧
    isRegularSubgroup H ∧
      Nonempty (H ≃* R)

/-- Conjugacy of regular copies inside the full automorphism group of a relation. -/
def conjugateRegularCopies (adj : R → R → Prop)
    (H K : Subgroup (Equiv.Perm R)) : Prop :=
  ∃ g : Equiv.Perm R,
    (∀ x y, adj x y ↔ adj (g x) (g y)) ∧
      ∀ h : Equiv.Perm R,
        h ∈ K ↔ ∃ q : Equiv.Perm R, q ∈ H ∧ h = g * q * g⁻¹

def oneRegularSubgroupConjugacyClass (adj : R → R → Prop) : Prop :=
  (∃ H : Subgroup (Equiv.Perm R), isRegularRSubgroup adj H) ∧
    ∀ H K : Subgroup (Equiv.Perm R),
      isRegularRSubgroup adj H →
        isRegularRSubgroup adj K → conjugateRegularCopies adj H K

/-- Babai's regular-subgroup conjugacy criterion for a Cayley digraph. -/
def babaiRegularSubgroupConjugacyCriterion (S : Set R) : Prop :=
  isDCI S ↔
    oneRegularSubgroupConjugacyClass (directedCayleyAdj S)

/-- The inverse-closed criterion for the underlying simple undirected Cayley graph. -/
def inverseClosedCISpecialization (S : Set R) : Prop :=
  inverseClosed S →
    (isCI S ↔ oneRegularSubgroupConjugacyClass (undirectedCayleyAdj S))

/-- Two nonconjugate regular copies obstruct the directed CI property. -/
def twoNonconjugateRegularCopiesObstructDCI (S : Set R) : Prop :=
  (∃ H K : Subgroup (Equiv.Perm R),
      isRegularRSubgroup (directedCayleyAdj S) H ∧
        isRegularRSubgroup (directedCayleyAdj S) K ∧
          ¬ conjugateRegularCopies (directedCayleyAdj S) H K) →
    ¬ isDCI S

/-- Under inverse closure, nonconjugate copies obstruct the undirected CI property. -/
def inverseClosedNonconjugateCopiesObstructCI (S : Set R) : Prop :=
  inverseClosed S →
    ((∃ H K : Subgroup (Equiv.Perm R),
        isRegularRSubgroup (undirectedCayleyAdj S) H ∧
          isRegularRSubgroup (undirectedCayleyAdj S) K ∧
            ¬ conjugateRegularCopies (undirectedCayleyAdj S) H K) →
      ¬ isCI S)

end MathlibPlus.Open.GroupTheory.CayleyCI
