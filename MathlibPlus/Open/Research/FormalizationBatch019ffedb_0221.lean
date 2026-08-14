import Mathlib

namespace MathlibPlus.Open.Research.Batch0221

open scoped BigOperators

noncomputable section

abbrev U : Type := Fin 3 → ZMod 5
abbrev V : Type := U × U

def F (z : U) : U :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

def q (p : V) : V := (p.2, p.1 + F p.2)

def claim6561 : Prop :=
  (∀ z : U, F z = ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]) ∧
    (∀ x z : U, q (x, z) = (z, x + F z))

def mixedDifferenceSet (z : U) : Set U :=
  {v | ∃ a : U,
    v = F (a + z) - F a - F z ∨ v = F (a - z) - F a - F (-z)}

def W (z : U) : Submodule (ZMod 5) U :=
  Submodule.span (ZMod 5) (mixedDifferenceSet z)

def fibre (z : U) : Set V := (W z : Set U) ×ˢ ({z} : Set U)

def e₁ : U := ![1, 0, 0]
def e₂ : U := ![0, 1, 0]
def e₃ : U := ![0, 0, 1]

def D : Set U := {e₁, e₂, e₃, e₂ + e₃}

def negSet {α : Type} [Neg α] (A : Set α) : Set α := Neg.neg '' A

def S : Set V := ⋃ z ∈ D ∪ negSet D, fibre z

def claim6563 : Prop :=
  (∀ z : U,
    W z = Submodule.span (ZMod 5)
      {v | ∃ a : U,
        v = F (a + z) - F a - F z ∨ v = F (a - z) - F a - F (-z)}) ∧
    (∀ z : U, fibre z = (W z : Set U) ×ˢ ({z} : Set U)) ∧
    D = {e₁, e₂, e₃, e₂ + e₃} ∧
    S = ⋃ z ∈ D ∪ negSet D, (W z : Set U) ×ˢ ({z} : Set U)

def claim6564 : Prop :=
  Module.finrank (ZMod 5) (W e₁) = 1 ∧
    Module.finrank (ZMod 5) (W e₂) = 2 ∧
    Module.finrank (ZMod 5) (W e₃) = 2 ∧
    Module.finrank (ZMod 5) (W (e₂ + e₃)) = 3

def pairedPiece (z : U) : Set V := fibre z ∪ fibre (-z)

def pairedCard (z : U) : Nat := Nat.card {v : V // v ∈ pairedPiece z}

def claim6565 : Prop :=
  pairedCard e₁ = 10 ∧ pairedCard e₂ = 50 ∧
    pairedCard e₃ = 50 ∧ pairedCard (e₂ + e₃) = 250

def claim6570 : Prop := q '' S = negSet (q '' S)

def cayleyAdj (A : Set V) (u v : V) : Prop := v - u ∈ A

def cayleyAutomorphism (A : Set V) (f : V → V) : Prop :=
  Function.Bijective f ∧ ∀ u v : V, cayleyAdj A u v ↔ cayleyAdj A (f u) (f v)

def qInv (u : V) : V := (u.2 - F u.1, u.1)

def inversion (u : V) : V := -u

def qConjugate (u : V) : V := q (-qInv u)

def claim6574 : Prop :=
  negSet S = S ∧ negSet (q '' S) = q '' S ∧
    cayleyAutomorphism S inversion ∧
    cayleyAutomorphism (q '' S) qConjugate

end
end MathlibPlus.Open.Research.Batch0221
