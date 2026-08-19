import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIElementaryAbelian3Rank7AllVerticalShearsClaim61332

noncomputable section

abbrev F3 := ZMod 3
abbrev A := Fin 3 → F3
abbrev B := Fin 4 → F3
abbrev V := B × A

/-- The fibre displacement submodule attached to a base direction. -/
def displacementSubmodule (F : B → A) (b : B) : Submodule F3 A :=
  Submodule.span F3
    {z : A | ∃ x : B, z = F b + F x - F (x + b)}

/-- The arbitrary vertical shear on the direct-sum carrier `B × A`. -/
def verticalShear (F : B → A) : V → V :=
  fun z => (z.1, z.2 + F z.1)

/-- The fibrewise map induced by a linear shadow of a vertical shear. -/
def linearVerticalShear (ell : B →ₗ[F3] A) : V → V :=
  fun z => (z.1, z.2 + ell z.1)

/-- A directed additive Cayley relation with connection set `S`. -/
def directedCayleyAdjacency (S : Set V) (x y : V) : Prop :=
  y - x ∈ S

/-- Isomorphism of directed additive Cayley relations. -/
def directedCayleyRelationIso (q : V → V) (S T : Set V) : Prop :=
  Function.Bijective q ∧
    ∀ x y : V,
      directedCayleyAdjacency S x y ↔
        directedCayleyAdjacency T (q x) (q y)

/-- Identity-free inverse-closed connection sets for ordinary undirected Cayley graphs. -/
def identityFree (S : Set V) : Prop :=
  (0 : V) ∉ S

def inverseClosed (S : Set V) : Prop :=
  ∀ ⦃s : V⦄, s ∈ S → -s ∈ S

/-- The ordinary undirected additive Cayley adjacency relation. -/
def undirectedCayleyAdjacency (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Isomorphism of ordinary undirected additive Cayley relations. -/
def undirectedCayleyRelationIso (q : V → V) (S T : Set V) : Prop :=
  Function.Bijective q ∧
    ∀ x y : V,
      undirectedCayleyAdjacency S x y ↔
        undirectedCayleyAdjacency T (q x) (q y)

/-- A vertical-shear witness to an ordinary undirected Cayley-CI defect. -/
def ordinaryUndirectedCayleyCIDefect
    (q : V → V) (S T : Set V) : Prop :=
  identityFree S ∧
    identityFree T ∧
    inverseClosed S ∧
    inverseClosed T ∧
    undirectedCayleyRelationIso q S T ∧
    ¬ ∃ e : V ≃+ V, (fun z => e z) '' S = T

/-- No ordinary undirected Cayley-CI defect can be witnessed by the shear. -/
def noOrdinaryUndirectedCayleyCIDefect (F : B → A) : Prop :=
  ∀ (S T : Set V),
    identityFree S →
    identityFree T →
    inverseClosed S →
    inverseClosed T →
    undirectedCayleyRelationIso (verticalShear F) S T →
      ¬ ordinaryUndirectedCayleyCIDefect (verticalShear F) S T

/-- Claim 61332: every normalized arbitrary vertical shear on `C_3^7` has
an exact linear connection-set shadow, with the stated ordinary undirected
Cayley-CI consequence. -/
def claim61332 : Prop :=
  ∀ (F : B → A),
    F 0 = 0 →
      ∃ ell : B →ₗ[F3] A,
        (∀ b : B,
          F b - ell b ∈ displacementSubmodule F b) ∧
        (∀ (S T : Set V),
          directedCayleyRelationIso (verticalShear F) S T →
            linearVerticalShear ell '' S = T) ∧
        noOrdinaryUndirectedCayleyCIDefect F

end

end MathlibPlus.Open.ResearchFormalization.CIElementaryAbelian3Rank7AllVerticalShearsClaim61332
