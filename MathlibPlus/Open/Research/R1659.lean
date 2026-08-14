import Mathlib

namespace MathlibPlus.Open.Research.R1659

abbrev D : Type := Fin 2 → ZMod 2
abbrev H : Type := Fin 3 → ZMod 3
abbrev G : Type := D × H

noncomputable def fiberCardinality (S : Set G) (h : H) : ℕ := by
  classical
  exact (Finset.univ.filter (fun d : D => (d, h) ∈ S)).card

def inverseClosed (S : Set G) : Prop :=
  ∀ g, g ∈ S → -g ∈ S

def cayleyAdjacent (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

def quotientColorRelation (S : Set G) (c : Fin 5) (h k : H) : Prop :=
  fiberCardinality S (k - h) = c.val

def cayleyIsomorphism (S : Set G) (φ : Equiv.Perm G) : Prop :=
  ∀ x y, cayleyAdjacent S x y ↔ cayleyAdjacent S (φ x) (φ y)

def blockPreserving (φ : Equiv.Perm G) (q : Equiv.Perm H) : Prop :=
  ∀ d h, (φ (d, h)).2 = q h

/-- The fiber cardinality is the five-color quotient relation, and a
block-preserving Cayley isomorphism preserves every color. -/
def claim33020 : Prop :=
  Fintype.card D = 4 ∧
    ∀ S : Set G, inverseClosed S →
      (∀ h : H, fiberCardinality S h ≤ 4) ∧
        ∀ (φ : Equiv.Perm G) (q : Equiv.Perm H),
          cayleyIsomorphism S φ →
            blockPreserving φ q →
              (∀ h k : H,
                fiberCardinality S (k - h) = fiberCardinality S (q k - q h)) ∧
                (∀ (c : Fin 5) (h k : H),
                  quotientColorRelation S c h k ↔
                    quotientColorRelation S c (q h) (q k))

def translateFinset (d : D) (s : Finset D) : Finset D :=
  s.image (fun x => d + x)

def translationEquivalent (s t : Finset D) : Prop :=
  ∃ d : D, translateFinset d s = t

/-- The sixteen subsets of the four-point Sylow-two factor have the stated
cardinality distribution and form seven translation orbits. -/
def claim33021 : Prop :=
  Fintype.card D = 4 ∧
    Fintype.card (Finset D) = 16 ∧
    Fintype.card {s : Finset D // s.card = 0} = 1 ∧
    Fintype.card {s : Finset D // s.card = 1} = 4 ∧
    Fintype.card {s : Finset D // s.card = 2} = 6 ∧
    Fintype.card {s : Finset D // s.card = 3} = 4 ∧
    Fintype.card {s : Finset D // s.card = 4} = 1 ∧
    (∃ reps : Fin 7 → Finset D,
      (∀ s : Finset D,
        ∃ i : Fin 7, ∃ d : D, translateFinset d (reps i) = s) ∧
        (∀ i j : Fin 7,
          translationEquivalent (reps i) (reps j) → i = j)) ∧
    (∃ s t : Finset D,
      s.card = t.card ∧ ¬ translationEquivalent s t)

/-- Origin-fixing permutations of the four-point elementary abelian group are
exactly its additive automorphisms, with the stated order. -/
def claim33024 : Prop :=
  Fintype.card {p : Equiv.Perm D // p 0 = 0} = 6 ∧
    Fintype.card (D ≃+ D) = 6 ∧
    (∀ p : Equiv.Perm D,
      p 0 = 0 → ∃ e : D ≃+ D, ∀ x : D, p x = e x) ∧
    (∀ p : Equiv.Perm D,
      p 0 = 0 → ∃ e : D ≃+ D, ∀ x : D, e (p x) = x)

end MathlibPlus.Open.Research.R1659
