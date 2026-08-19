import Mathlib

open scoped BigOperators
open scoped LinearAlgebra.Projectivization

namespace MathlibPlus.Open.ResearchFormalization.MMEvenFamily61365

abbrev F3 := ZMod 3
abbrev mmA := Fin 3 → F3
abbrev mmB := Fin 3 → F3
abbrev mmV := mmA × mmB
abbrev mmProjectivePoint := ℙ F3 mmB

/-- The extension of a projective row function to the zero vector and to
all nonzero vectors. -/
def extendedRow (g : mmProjectivePoint → F3) (b : mmB) : F3 :=
  if h : b = 0 then 0 else g (Projectivization.mk F3 b h)

/-- The even Maiorana--McFarland function attached to a projective row. -/
def mmFunction (g : mmProjectivePoint → F3) (v : mmV) : F3 :=
  (∑ i : Fin 3, v.1 i * v.2 i) + extendedRow g v.2

/-- The value-fusion connection set, with the identity removed. -/
def mmConnectionSet (g : mmProjectivePoint → F3)
    (C : Set F3) : Set mmV :=
  {v | v ≠ 0 ∧ mmFunction g v ∈ C}

/-- Identity-free and inverse-closed predicates for the family. -/
def identityFree (S : Set mmV) : Prop :=
  S ⊆ (Set.univ : Set mmV) \ {0}

def inverseClosed (S : Set mmV) : Prop :=
  ∀ v : mmV, v ∈ S ↔ -v ∈ S

/-- Ordinary undirected Cayley adjacency on the additive vector group. -/
def cayleyAdjacency (S : Set mmV) (x y : mmV) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- An arbitrary graph isomorphism between two Cayley presentations. -/
def cayleyGraphIsomorphism (S T : Set mmV) : Prop :=
  ∃ e : Equiv.Perm mmV,
    ∀ x y,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

/-- Claim 61365: the thirteen-point even Maiorana--McFarland family,
including every value fusion, has actual linear transporters. -/
def claim61365 : Prop :=
  Nat.card mmProjectivePoint = 13 ∧
    Nat.card (mmProjectivePoint → F3) = 1594323 ∧
    (∀ (g : mmProjectivePoint → F3) (b : mmB),
      extendedRow g (-b) = extendedRow g b) ∧
    (∀ (g : mmProjectivePoint → F3) (a : mmA),
      mmFunction g (a, 0) = 0) ∧
    (∀ (g : mmProjectivePoint → F3) (C : Set F3),
      identityFree (mmConnectionSet g C) ∧
        inverseClosed (mmConnectionSet g C)) ∧
    ∀ (g h : mmProjectivePoint → F3) (C : Set F3),
      cayleyGraphIsomorphism
          (mmConnectionSet g C) (mmConnectionSet h C) →
        ∃ L : mmV ≃ₗ[F3] mmV,
          L '' mmConnectionSet g C = mmConnectionSet h C

end MathlibPlus.Open.ResearchFormalization.MMEvenFamily61365
