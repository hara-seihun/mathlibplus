import Mathlib

open Classical
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1210Claim32273

abbrev A7 := Fin 2 → ZMod 7

/-- The block of the translation development indexed by `t`. -/
def translated (B : Finset A7) (t : A7) : Finset A7 :=
  B.image (fun b => b + t)

/-- The two-sided incidence relation of the translation development. -/
def developmentAdj (B : Finset A7) (p q : A7 × Bool) : Prop :=
  (p.2 = false ∧ q.2 = true ∧ q.1 - 2 • p.1 ∈ B) ∨
    (p.2 = true ∧ q.2 = false ∧ p.1 - 2 • q.1 ∈ B)

/-- The vertex map with independently specified permutations on the two sides. -/
def sideMap (psi0 psi1 : Equiv.Perm A7)
    (p : A7 × Bool) : A7 × Bool :=
  if p.2 then (psi1 p.1, true) else (psi0 p.1, false)

/-- Side-preserving isomorphism of the displayed incidence relations. -/
def sidePreservingDevelopmentIso
    (B C : Finset A7) (psi0 psi1 : Equiv.Perm A7) : Prop :=
  ∀ p q,
    developmentAdj B p q ↔
      developmentAdj C (sideMap psi0 psi1 p) (sideMap psi0 psi1 q)

/-- Existence of a side-preserving isomorphism between two developments. -/
def developmentEquivalent (B C : Finset A7) : Prop :=
  ∃ psi0 psi1 : Equiv.Perm A7,
    sidePreservingDevelopmentIso B C psi0 psi1

/-- The translated subset appearing in the adjacent-profile equation. -/
def adjacentProfileEquation
    (B C : Finset A7) (psi0 psi1 : Equiv.Perm A7) : Prop :=
  ∀ y : A7,
    (translated B (2 • y)).image psi1 =
      translated C (2 • psi0 y)

/-- Claim 32273: the concrete 98-vertex development has two 49-point sides,
and the adjacent normalized-profile equation is exactly its side-preserving
isomorphism condition. -/
def sideColoredTranslationDevelopment_claim32273 : Prop :=
  Fintype.card A7 = 49 ∧
    Fintype.card (A7 × Bool) = 98 ∧
    ∀ (B C : Finset A7) (psi0 psi1 : Equiv.Perm A7),
      adjacentProfileEquation B C psi0 psi1 ↔
        sidePreservingDevelopmentIso B C psi0 psi1

end MathlibPlus.Open.ResearchFormalization.R1210Claim32273
