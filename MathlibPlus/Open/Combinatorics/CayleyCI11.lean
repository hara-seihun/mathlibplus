import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Combinatorics.CayleyCI11

abbrev G := ZMod 11

def inverseClosed (S : Set G) : Prop :=
  S ⊆ (Set.univ : Set G) \ {0} ∧ ∀ x : G, x ∈ S ↔ -x ∈ S

def cayleyGraphIsomorphism (S T : Set G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y : G, x ≠ y → (y - x ∈ S ↔ f y - f x ∈ T)

def pair (i : Fin 5) : Set G :=
  {x | x = (i.val + 1 : G) ∨ x = -(i.val + 1 : G)}

def wordConnection (b : Fin 32) : Set G :=
  {x | ∃ i : Fin 5,
    b.val / 2 ^ (4 - i.val) % 2 = 1 ∧ x ∈ pair i}

def graphFiber (b : Fin 32) : Set (Fin 32) :=
  {b' | cayleyGraphIsomorphism (wordConnection b) (wordConnection b')}

def unitImage (u : G) (S : Set G) : Set G :=
  (fun x : G => u * x) '' S

def additiveAutImage (e : G ≃+ G) (S : Set G) : Set G :=
  e '' S

def additiveAutOrbit (b : Fin 32) : Set (Fin 32) :=
  {b' | ∃ e : G ≃+ G, wordConnection b' = additiveAutImage e (wordConnection b)}

def expectedFibers : Set (Set (Fin 32)) :=
  {F |
    F = ({0} : Set (Fin 32)) ∨
      F = ({1, 2, 4, 8, 16} : Set (Fin 32)) ∨
        F = ({3, 9, 12, 18, 20} : Set (Fin 32)) ∨
          F = ({5, 6, 10, 17, 24} : Set (Fin 32)) ∨
            F = ({7, 14, 21, 25, 26} : Set (Fin 32)) ∨
              F = ({11, 13, 19, 22, 28} : Set (Fin 32)) ∨
                F = ({15, 23, 27, 29, 30} : Set (Fin 32)) ∨
                  F = ({31} : Set (Fin 32))}

def wordEncodingIsComplete : Prop :=
  Function.Injective wordConnection ∧
    (∀ b : Fin 32, inverseClosed (wordConnection b)) ∧
      ∀ S : Set G, inverseClosed S → ∃ b : Fin 32, wordConnection b = S

def everyCayleyGraphIsCI : Prop :=
  ∀ S : Set G, inverseClosed S →
    ∀ T : Set G, inverseClosed T →
      cayleyGraphIsomorphism S T →
        ∃ e : G ≃+ G, T = additiveAutImage e S

def isUndirectedCIGroup : Prop :=
  ∀ S T : Set G,
    inverseClosed S → inverseClosed T → cayleyGraphIsomorphism S T →
      ∃ e : G ≃+ G, T = additiveAutImage e S

def cayleyCI11Claim : Prop :=
  (∀ S T : Set G,
      inverseClosed S →
        inverseClosed T →
          (cayleyGraphIsomorphism S T ↔ ∃ u : G, IsUnit u ∧ T = unitImage u S)) ∧
    wordEncodingIsComplete ∧
      (Set.range graphFiber = expectedFibers) ∧
        (∀ b : Fin 32, graphFiber b = additiveAutOrbit b) ∧
        everyCayleyGraphIsCI ∧ isUndirectedCIGroup

end MathlibPlus.Open.Combinatorics.CayleyCI11
