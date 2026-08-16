import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The free generators named `a` and `t` in the displayed presentation. -/
def ec35GeneratorA : FreeGroup (Fin 2) := FreeGroup.of (0 : Fin 2)

def ec35GeneratorT : FreeGroup (Fin 2) := FreeGroup.of (1 : Fin 2)

/-- Relators for the displayed presentation of `E(C₃₅,8)`. -/
def EC35EightRelators : Set (FreeGroup (Fin 2)) :=
  {ec35GeneratorA ^ 35, ec35GeneratorT ^ 8,
    ec35GeneratorT * ec35GeneratorA * ec35GeneratorT⁻¹ * ec35GeneratorA}

abbrev EC35EightNormal : Subgroup (FreeGroup (Fin 2)) :=
  Subgroup.normalClosure EC35EightRelators

/-- The group in the displayed presentation `⟨a,t | a^35=t^8=1,
`tat⁻¹=a⁻¹⟩`. -/
abbrev EC35Eight := FreeGroup (Fin 2) ⧸ EC35EightNormal

def ec35A : EC35Eight := QuotientGroup.mk ec35GeneratorA

def ec35T : EC35Eight := QuotientGroup.mk ec35GeneratorT

/-- Right-multiplication adjacency for an ordinary undirected Cayley graph. -/
def EC35CayleyAdj (S : Set EC35Eight) (x y : EC35Eight) : Prop :=
  ∃ s ∈ S, y = x * s

/-- Isomorphism of the Cayley graphs determined by two connection sets. -/
def EC35CayleyIsomorphic (S T : Set EC35Eight) : Prop :=
  ∃ e : EC35Eight ≃ EC35Eight,
    ∀ x y : EC35Eight,
      EC35CayleyAdj S x y ↔ EC35CayleyAdj T (e x) (e y)

/-- Every identity-free inverse-closed connection set of valency 2, 3, 4, or 5
on the displayed group is a CI-set. -/
def EC35EightLowValencyCI : Prop :=
  ∀ S T : Set EC35Eight,
    (1 : EC35Eight) ∉ S →
    (1 : EC35Eight) ∉ T →
    (∀ s ∈ S, s⁻¹ ∈ S) →
    (∀ t ∈ T, t⁻¹ ∈ T) →
    S.ncard = T.ncard →
    (S.ncard = 2 ∨ S.ncard = 3 ∨ S.ncard = 4 ∨ S.ncard = 5) →
    EC35CayleyIsomorphic S T →
    ∃ α : EC35Eight ≃* EC35Eight, α '' S = T

end MathlibPlus.Open.GraphTheory
