import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-! The exact additive Cayley-graph semantics used for the odd C₄-coset claim. -/

abbrev claim60975V := Fin 3 → ZMod 3

abbrev claim60975G := ZMod 4 × claim60975V

def claim60975H : Set claim60975G :=
  {g | g.1 = 0 ∨ g.1 = 2}

def claim60975O : Set claim60975G :=
  {g | g.1 = 1 ∨ g.1 = 3}

def claim60975IdentityFree (S : Set claim60975G) : Prop :=
  (0 : claim60975G) ∉ S

def claim60975InverseClosed (S : Set claim60975G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def claim60975Adj (R : Set claim60975G) (x y : claim60975G) : Prop :=
  x ≠ y ∧ y - x ∈ R

def claim60975GraphIso (R T : Set claim60975G) : Prop :=
  ∃ f : claim60975G → claim60975G,
    Function.Bijective f ∧
      ∀ x y, claim60975Adj R x y ↔ claim60975Adj T (f x) (f y)

def claim60975OrdinaryUndirectedCI (R : Set claim60975G) : Prop :=
  claim60975IdentityFree R ∧
    claim60975InverseClosed R ∧
    ∀ T : Set claim60975G,
      claim60975IdentityFree T →
      claim60975InverseClosed T →
      claim60975GraphIso R T →
      ∃ α : claim60975G ≃+ claim60975G, α '' R = T

def claim60975OrdinaryComplement (S : Set claim60975G) : Set claim60975G :=
  (Set.univ \ ({0} : Set claim60975G)) \ S

def claim60975 : Prop :=
  ∀ S : Set claim60975G,
    S ⊆ claim60975O →
    claim60975IdentityFree S →
    claim60975InverseClosed S →
    claim60975OrdinaryUndirectedCI S ∧
      claim60975OrdinaryUndirectedCI (claim60975OrdinaryComplement S)

end MathlibPlus.Open.ResearchFormalization
