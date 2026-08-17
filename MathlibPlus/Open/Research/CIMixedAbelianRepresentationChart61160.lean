import Mathlib

namespace MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160

noncomputable section

abbrev F2 := ZMod 2
abbrev F3 := ZMod 3
abbrev A := Fin 4 → F2
abbrev B := Fin 2 → F3
abbrev G := A × B
abbrev AffineGroup := A ≃ᵃ[F2] A
abbrev LinearAutomorphism := (A ≃ₗ[F2] A) × (B ≃ₗ[F3] B)

-- The affine representation and the pointed base permutation.
def affineRepresentation (rho : B → AffineGroup) : Prop :=
  (∀ b : B, ∃ L : A ≃ₗ[F2] A, ∃ c : A,
    ∀ a : A, rho b a = L a + c) ∧
  rho 0 = 1 ∧
  ∀ b d : B, rho (b + d) = rho b * rho d

def pointedBasePermutation (sigma : B ≃ B) : Prop :=
  sigma 0 = 0

def pointedMap (rho : B → AffineGroup) (sigma : B ≃ B) : G → G :=
  fun p => (rho p.2 p.1, sigma p.2)

-- The displayed fibrewise affine map is a permutation of the direct product.
def pointedPermutation (rho : B → AffineGroup) (sigma : B ≃ B) : G ≃ G :=
  (Equiv.prodComm A B).trans
    ((Equiv.sigmaEquivProd B A).symm.trans
      ((Equiv.sigmaCongr sigma (fun b => (rho b).toEquiv)).trans
        ((Equiv.sigmaEquivProd B A).trans (Equiv.prodComm B A))))

-- Inverse atoms are the sets [d]={d,-d} away from the identity.
def inverseAtomSet (D : Set G) : Prop :=
  ∃ d : G, d ≠ 0 ∧ D = ({d, -d} : Set G)

abbrev InverseAtom := {D : Set G // inverseAtomSet D}

-- E_D is the unordered edge atom attached to an inverse atom D.
def edgeAtom (D : InverseAtom) : Set (Set G) :=
  {E | ∃ d : G, d ∈ D.1 ∧ ∃ x : G, E = ({x, x + d} : Set G)}

def incidence (f : G ≃ G) (D D' : InverseAtom) : Prop :=
  ∃ E : Set G, E ∈ edgeAtom D ∧ f '' E ∈ edgeAtom D'

abbrev IncidenceNode := InverseAtom × Bool

def incidenceAdj (f : G ≃ G) (u v : IncidenceNode) : Prop :=
  (u.2 = true ∧ v.2 = false ∧ incidence f u.1 v.1) ∨
  (u.2 = false ∧ v.2 = true ∧ incidence f v.1 u.1)

def incidenceReachable (f : G ≃ G) (u v : IncidenceNode) : Prop :=
  Relation.ReflTransGen (incidenceAdj f) u v

def incidenceComponent (f : G ≃ G) (C : Set IncidenceNode) : Prop :=
  ∃ u : IncidenceNode, C = {v | incidenceReachable f u v}

abbrev IncidenceComponent (f : G ≃ G) :=
  {C : Set IncidenceNode // incidenceComponent f C}

def sourceLabels {f : G ≃ G} (C : IncidenceComponent f) : Set InverseAtom :=
  {D | (D, true) ∈ C.1}

def targetLabels {f : G ≃ G} (C : IncidenceComponent f) : Set InverseAtom :=
  {D | (D, false) ∈ C.1}

def sourceConnectionSet {f : G ≃ G}
    (K : Set (IncidenceComponent f)) : Set G :=
  {g | ∃ C : IncidenceComponent f, C ∈ K ∧
    ∃ D : InverseAtom, D ∈ sourceLabels C ∧ g ∈ D.1}

def targetConnectionSet {f : G ≃ G}
    (K : Set (IncidenceComponent f)) : Set G :=
  {g | ∃ C : IncidenceComponent f, C ∈ K ∧
    ∃ D : InverseAtom, D ∈ targetLabels C ∧ g ∈ D.1}

-- The ordinary undirected Cayley relation and its labelled graph isomorphism.
def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def ordinaryGraphIsomorphism (f : G ≃ G) (S T : Set G) : Prop :=
  ∀ x y : G, cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def identityFree (S : Set G) : Prop :=
  (0 : G) ∉ S

def inverseClosed (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

-- Aut(G)=GL(4,2)×GL(2,3), acting componentwise on G and on inverse atoms.
def groupAutomorphismAction (alpha : LinearAutomorphism) : G ≃+ G :=
  AddEquiv.prodCongr alpha.1.toAddEquiv alpha.2.toAddEquiv

def alphaLabelImage (alpha : LinearAutomorphism)
    (I : Set InverseAtom) : Set InverseAtom :=
  {E | ∃ D : InverseAtom, D ∈ I ∧
    groupAutomorphismAction alpha '' D.1 = E.1}

def commonComponentShadow (rho : B → AffineGroup) (sigma : B ≃ B) : Prop :=
  let f := pointedPermutation rho sigma
  ∃ alpha : LinearAutomorphism,
    (∀ C : IncidenceComponent f,
      alphaLabelImage alpha (sourceLabels C) = targetLabels C) ∧
    (∀ K : Set (IncidenceComponent f),
      ordinaryGraphIsomorphism f
        (sourceConnectionSet K) (targetConnectionSet K) ∧
      groupAutomorphismAction alpha '' sourceConnectionSet K =
        targetConnectionSet K)

def chartDefect (rho : B → AffineGroup) (sigma : B ≃ B) : Prop :=
  let f := pointedPermutation rho sigma
  ∃ K : Set (IncidenceComponent f),
    let S := sourceConnectionSet K
    let T := targetConnectionSet K
    identityFree S ∧ inverseClosed S ∧
      identityFree T ∧ inverseClosed T ∧
      ordinaryGraphIsomorphism f S T ∧
      ¬ ∃ alpha : LinearAutomorphism,
        groupAutomorphismAction alpha '' S = T

-- Every affine-representation chart has one common automorphism shadow, for all
-- incidence components and all unions of components; hence it supplies no CI defect.
def claim_61160 : Prop :=
  ∀ (rho : B → AffineGroup) (sigma : B ≃ B),
    affineRepresentation rho →
    pointedBasePermutation sigma →
    commonComponentShadow rho sigma ∧
      ¬ chartDefect rho sigma

end
end MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160
