import Mathlib

namespace MathlibPlus.Open.GraphTheory.CIMixedAbelianTranslationChartCommonShadow

abbrev A : Type := Fin 4 → ZMod 2
abbrev B : Type := Fin 2 → ZMod 3
abbrev G : Type := A × B

/-- A nonidentity inverse atom in the additive group `X`. -/
def inverseAtomPredicate {X : Type*} [AddGroup X] [DecidableEq X]
    (D : Finset X) : Prop :=
  ∃ d : X, d ≠ 0 ∧ D = ({d, -d} : Finset X)

abbrev InverseAtom (X : Type*) [AddGroup X] [DecidableEq X] :=
  {D : Finset X // inverseAtomPredicate D}

/-- The unordered edge atom attached to an inverse atom. -/
def edgeAtom {X : Type*} [AddGroup X] [DecidableEq X]
    (D : InverseAtom X) : Set (Sym2 X) :=
  {e | ∃ d ∈ D.1, ∃ x : X, e = Sym2.mk x (x + d)}

/-- Nonempty intersection of the image of one edge atom with another. -/
def atomImageIntersects {X : Type*} [AddGroup X] [DecidableEq X]
    (f : X → X) (D E : InverseAtom X) : Prop :=
  ∃ e : Sym2 X, e ∈ edgeAtom D ∧ Sym2.map f e ∈ edgeAtom E

abbrev IncidenceVertex := Bool × InverseAtom G

/-- The symmetric bipartite incidence relation of a pointed chart. -/
def atomIncidenceAdj (f : G → G)
    (v w : IncidenceVertex) : Prop :=
  (v.1 = false ∧ w.1 = true ∧ atomImageIntersects f v.2 w.2) ∨
    (v.1 = true ∧ w.1 = false ∧ atomImageIntersects f w.2 v.2)

/-- The connected component represented by a vertex. -/
def incidenceComponent (f : G → G) (v : IncidenceVertex) :
    Set IncidenceVertex :=
  {w | Relation.EqvGen (atomIncidenceAdj f) v w}

def isIncidenceComponent (f : G → G)
    (C : Set IncidenceVertex) : Prop :=
  ∃ v, C = incidenceComponent f v

def isComponentCollection (f : G → G)
    (K : Set (Set IncidenceVertex)) : Prop :=
  ∀ C ∈ K, isIncidenceComponent f C

/-- Source-side inverse-atom labels of a component. -/
def sourceLabels (f : G → G) (C : Set IncidenceVertex) : Set (Finset G) :=
  {D | ∃ A : InverseAtom G, (false, A) ∈ C ∧ D = A.1}

/-- Target-side inverse-atom labels of a component. -/
def targetLabels (f : G → G) (C : Set IncidenceVertex) : Set (Finset G) :=
  {D | ∃ A : InverseAtom G, (true, A) ∈ C ∧ D = A.1}

/-- The action of an additive automorphism on inverse-atom labels. -/
def atomImageSet (α : G ≃+ G) (I : Set (Finset G)) : Set (Finset G) :=
  {E | ∃ D : InverseAtom G, D.1 ∈ I ∧
    E = D.1.map α.toEquiv.toEmbedding}

abbrev fibreChart (c : B → A) (σ : Equiv.Perm B) : G → G :=
  fun x => (x.1 + c x.2, σ x.2)

def selectedSourceSet (f : G → G)
    (K : Set (Set IncidenceVertex)) : Set G :=
  {g | ∃ C ∈ K, ∃ D ∈ sourceLabels f C, g ∈ D}

def selectedTargetSet (f : G → G)
    (K : Set (Set IncidenceVertex)) : Set G :=
  {g | ∃ C ∈ K, ∃ D ∈ targetLabels f C, g ∈ D}

/-- Adjacency in an ordinary undirected additive Cayley graph. -/
def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyGraphIsomorphism (f : G → G) (S T : Set G) : Prop :=
  Function.Bijective f ∧
    ∀ x y : G,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def identityFree (S : Set G) : Prop :=
  (0 : G) ∉ S

def inverseClosed (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

def ordinaryCayleyCIDefect (f : G → G) (S T : Set G) : Prop :=
  identityFree S ∧ identityFree T ∧ inverseClosed S ∧ inverseClosed T ∧
    cayleyGraphIsomorphism f S T ∧
    ¬ ∃ α : G ≃+ G, Set.image (fun x => α x) S = T

/-- The product of the two linear automorphism factors of `G`. -/
def productAutomorphism
    (u : A ≃ₗ[ZMod 2] A) (v : B ≃ₗ[ZMod 3] B) : G ≃+ G :=
  u.toAddEquiv.prodCongr v.toAddEquiv

/-- Claim 61161: every unrestricted pointed fibre-translation chart on
`F₂⁴ × F₃²` has one additive automorphism shadowing all incidence components
and all unions of those components. -/
def claim61161 : Prop :=
  ∀ (c : B → A) (σ : Equiv.Perm B),
    c 0 = 0 →
    σ 0 = 0 →
    ∃ (u : A ≃ₗ[ZMod 2] A) (v : B ≃ₗ[ZMod 3] B),
      let α : G ≃+ G := productAutomorphism u v
      (∀ C : Set IncidenceVertex,
        isIncidenceComponent (fibreChart c σ) C →
          targetLabels (fibreChart c σ) C =
            atomImageSet α (sourceLabels (fibreChart c σ) C)) ∧
      (∀ K : Set (Set IncidenceVertex),
        isComponentCollection (fibreChart c σ) K →
          let S := selectedSourceSet (fibreChart c σ) K
          let T := selectedTargetSet (fibreChart c σ) K
          cayleyGraphIsomorphism (fibreChart c σ) S T ∧
            Set.image (fun x => α x) S = T ∧
            ¬ ordinaryCayleyCIDefect (fibreChart c σ) S T)

end MathlibPlus.Open.GraphTheory.CIMixedAbelianTranslationChartCommonShadow
