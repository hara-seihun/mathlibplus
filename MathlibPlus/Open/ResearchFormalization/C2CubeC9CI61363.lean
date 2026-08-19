import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C2CubeC9CI61363

abbrev binaryCube := Fin 3 → ZMod 2
abbrev c2CubeC9Group := binaryCube × ZMod 9

/-- Identity-free connection sets on the additive group `C₂^3 × C₉`. -/
def identityFree (S : Set c2CubeC9Group) : Prop :=
  S ⊆ (Set.univ : Set c2CubeC9Group) \ {0}

/-- Inverse closure for an additive connection set. -/
def inverseClosed (S : Set c2CubeC9Group) : Prop :=
  ∀ s : c2CubeC9Group, s ∈ S ↔ -s ∈ S

/-- Adjacency in the ordinary undirected additive Cayley graph. -/
def cayleyAdjacency (S : Set c2CubeC9Group)
    (x y : c2CubeC9Group) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Isomorphism of two ordinary undirected Cayley graphs on the common group. -/
def cayleyGraphIsomorphism (S T : Set c2CubeC9Group) : Prop :=
  ∃ e : Equiv.Perm c2CubeC9Group,
    ∀ x y,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

/-- The explicit automorphism-group factorization in the admitted claim. -/
def automorphismFactorization : Prop :=
  Nonempty
    (Multiplicative (AddAut c2CubeC9Group) ≃*
      ((Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) × (ZMod 9)ˣ))

/-- Claim 61363: every identity-free inverse-closed Cayley graph on
`C₂^3 × C₉` is carried to any isomorphic one by an additive group
automorphism, with no valency or generation restriction. -/
def claim61363 : Prop :=
  Nat.card c2CubeC9Group = 72 ∧
    Nat.card (AddAut c2CubeC9Group) = 1008 ∧
    automorphismFactorization ∧
    ∀ (S T : Set c2CubeC9Group),
      identityFree S →
      inverseClosed S →
      identityFree T →
      inverseClosed T →
      cayleyGraphIsomorphism S T →
      ∃ α : AddAut c2CubeC9Group, α '' S = T

end MathlibPlus.Open.ResearchFormalization.C2CubeC9CI61363
