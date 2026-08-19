import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1199Claim32136

abbrev C2Part := Fin 3 → ZMod 2
abbrev C3Part := Fin 2 → ZMod 3
abbrev G := C2Part × C3Part

abbrev ConnectionSet :=
  {S : Finset G //
    0 ∉ S ∧
      (∀ x : G, x ∈ S ↔ -x ∈ S) ∧
      (S.card = 11 ∨ S.card = 12)}

def cayleyAdj (S : ConnectionSet) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S.1

def fullGraphGroup (S : ConnectionSet) : Set (Equiv.Perm G) :=
  {p | ∀ x y : G,
    cayleyAdj S x y ↔ cayleyAdj S (p x) (p y)}

def naturalRegularCopy : Set (Equiv.Perm G) :=
  Set.range (fun a : G => Equiv.addRight a)

def isPermutationSubgroup (H : Set (Equiv.Perm G)) : Prop :=
  1 ∈ H ∧
    (∀ p q, p ∈ H → q ∈ H → p * q ∈ H) ∧
      ∀ p, p ∈ H → p⁻¹ ∈ H

def isRegularCopy (H : Set (Equiv.Perm G)) : Prop :=
  isPermutationSubgroup H ∧
    ∃ ρ : G → Equiv.Perm G,
      Function.Injective ρ ∧
        (∀ a b : G, ρ (a + b) = ρ a * ρ b) ∧
          Set.range ρ = H ∧
            ∀ x y : G, ∃! a : G, ρ a x = y

def fullGroupNonnormal (S : ConnectionSet) : Prop :=
  naturalRegularCopy ⊆ fullGraphGroup S ∧
    ¬ (∀ p, p ∈ fullGraphGroup S →
        ∀ t, t ∈ naturalRegularCopy → p * t * p⁻¹ ∈ naturalRegularCopy)

def classifiedNonnormalFullGroups : Set (Set (Equiv.Perm G)) :=
  {H | ∃ S : ConnectionSet,
    fullGroupNonnormal S ∧ H = fullGraphGroup S}

/-- Claim 32136: the finite scope is the ordinary undirected
valency-eleven/twelve boundary on `C₂³ × C₃²`, with the natural regular copy
as reference and the nonnormal full graph groups as the classified class. -/
def claim32136_finiteLowBoundaryConnectionSpace : Prop :=
  Fintype.card G = 72 ∧
    isRegularCopy naturalRegularCopy ∧
      (∀ S : ConnectionSet,
        naturalRegularCopy ⊆ fullGraphGroup S) ∧
        classifiedNonnormalFullGroups.Nonempty

end MathlibPlus.Open.ResearchFormalization.R1199Claim32136
