import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1199.Claim41907

noncomputable section

/-- The exact additive group `C₂³ × C₃²`. -/
abbrev C2Part := Fin 3 → ZMod 2
abbrev C3Part := Fin 2 → ZMod 3
abbrev G := C2Part × C3Part

/-- Identity-free inverse-closed connection sets at the two admitted
low-boundary valencies. -/
abbrev ConnectionSet :=
  {S : Finset G //
    0 ∉ S ∧
      (∀ x : G, x ∈ S ↔ -x ∈ S) ∧
      (S.card = 11 ∨ S.card = 12)}

/-- The ordinary undirected Cayley adjacency relation on the exact carrier. -/
def cayleyAdj (S : ConnectionSet) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S.1

def ordinaryUndirectedCayley (S : ConnectionSet) : Prop :=
  ∀ x y : G, cayleyAdj S x y ↔ cayleyAdj S y x

/-- The full graph-automorphism set of the actual Cayley graph. -/
def fullGraphGroup (S : ConnectionSet) : Set (Equiv.Perm G) :=
  {p | ∀ x y : G,
    cayleyAdj S x y ↔ cayleyAdj S (p x) (p y)}

/-- The natural regular translation copy used as the reference subgroup. -/
def naturalTranslation (a : G) : Equiv.Perm G :=
  Equiv.addRight a

def naturalRegularCopy : Set (Equiv.Perm G) :=
  Set.range naturalTranslation

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

/-- Nonnormality of the natural regular copy inside the full graph group. -/
def fullGroupNonnormal (S : ConnectionSet) : Prop :=
  naturalRegularCopy ⊆ fullGraphGroup S ∧
    ¬ (∀ p, p ∈ fullGraphGroup S →
      ∀ t, t ∈ naturalRegularCopy → p * t * p⁻¹ ∈ naturalRegularCopy)

/-- Claim 41907: the finite scope is the exact order-72 additive carrier,
ordinary undirected identity-free inverse-closed Cayley connection sets at
valencies eleven and twelve, restricted to nonnormal full graph groups with
the natural regular copy as reference.  Directed relations, valencies
thirteen through fifty-eight, arbitrary imprimitive overgroups, and the
residual all-order mixed-abelian `A₅` shell are outside the quantified scope. -/
def claim41907 : Prop :=
  Fintype.card G = 72 ∧
    ∀ S : ConnectionSet,
      fullGroupNonnormal S →
        ordinaryUndirectedCayley S ∧
          (S.1.card = 11 ∨ S.1.card = 12) ∧
            isRegularCopy naturalRegularCopy ∧
              naturalRegularCopy ⊆ fullGraphGroup S ∧
                ¬ (∀ p, p ∈ fullGraphGroup S →
                  ∀ t, t ∈ naturalRegularCopy →
                    p * t * p⁻¹ ∈ naturalRegularCopy)

end

end MathlibPlus.Open.ResearchFormalization.R1199.Claim41907
