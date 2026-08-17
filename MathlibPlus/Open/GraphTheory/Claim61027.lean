import Mathlib

open Set

namespace MathlibPlus.Open.GraphTheory.Claim61027

noncomputable section

/-- A finset is an inverse atom when it is the unordered pair of a
nonidentity element and its inverse.  An involution consequently gives a
singleton atom. -/
def inverseAtomPredicate {G : Type*} [Group G] [DecidableEq G]
    (D : Finset G) : Prop :=
  ∃ d : G, d ≠ 1 ∧ D = {d, d⁻¹}

abbrev InverseAtom (G : Type*) [Group G] [DecidableEq G] :=
  {D : Finset G // inverseAtomPredicate D}

/-- The unordered right-Cayley edge atom belonging to an inverse atom. -/
def edgeAtom {G : Type*} [Group G] [DecidableEq G]
    (D : InverseAtom G) : Set (Sym2 G) :=
  {e | ∃ d ∈ D.1, ∃ x : G, e = Sym2.mk x (x * d)}

/-- Incidence between a source atom and a target atom under a permutation. -/
def atomImageIntersects {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (D E : InverseAtom G) : Prop :=
  ∃ e : Sym2 G,
    e ∈ edgeAtom D ∧ Sym2.map f e ∈ edgeAtom E

abbrev IncidenceVertex (G : Type*) [Group G] [DecidableEq G] :=
  Bool × InverseAtom G

/-- The symmetric bipartite incidence relation, with `false` as source and
`true` as target. -/
def atomIncidenceAdj {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (v w : IncidenceVertex G) : Prop :=
  (v.1 = false ∧ w.1 = true ∧ atomImageIntersects f v.2 w.2) ∨
    (v.1 = true ∧ w.1 = false ∧ atomImageIntersects f w.2 v.2)

/-- The connected component represented by a vertex of the incidence graph. -/
def incidenceComponent {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (v : IncidenceVertex G) : Set (IncidenceVertex G) :=
  {w | Relation.EqvGen (atomIncidenceAdj f) v w}

def isIncidenceComponent {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (C : Set (IncidenceVertex G)) : Prop :=
  ∃ v, C = incidenceComponent f v

def isComponentCollection {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (𝒦 : Set (Set (IncidenceVertex G))) : Prop :=
  ∀ C ∈ 𝒦, isIncidenceComponent f C

/-- The source-side atom labels of a component. -/
def sourceLabels {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (C : Set (IncidenceVertex G)) : Set (Finset G) :=
  {D | ∃ A : InverseAtom G, (false, A) ∈ C ∧ D = A.1}

/-- The target-side atom labels of a component. -/
def targetLabels {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (C : Set (IncidenceVertex G)) : Set (Finset G) :=
  {D | ∃ A : InverseAtom G, (true, A) ∈ C ∧ D = A.1}

/-- The image of a set of atom labels under a group automorphism. -/
def atomImageSet {G : Type*} [Group G] [DecidableEq G]
    (α : G ≃* G) (I : Set (Finset G)) : Set (Finset G) :=
  {E | ∃ D : InverseAtom G, D.1 ∈ I ∧
    E = D.1.map α.toEquiv.toEmbedding}

/-- The connection set obtained from source labels in a selected collection
of components. -/
def selectedSourceSet {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (𝒦 : Set (Set (IncidenceVertex G))) : Set G :=
  {g | ∃ C ∈ 𝒦, ∃ D ∈ sourceLabels f C, g ∈ D}

/-- The connection set obtained from target labels in a selected collection
of components. -/
def selectedTargetSet {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (𝒦 : Set (Set (IncidenceVertex G))) : Set G :=
  {g | ∃ C ∈ 𝒦, ∃ D ∈ targetLabels f C, g ∈ D}

/-- Right-Cayley adjacency for a connection set. -/
def cayleyAdjacency {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

/-- The pointed permutation is a Cayley-graph isomorphism between the two
connection sets. -/
def cayleyGraphIsomorphism {G : Type*} [Group G]
    (f : Equiv.Perm G) (S T : Set G) : Prop :=
  ∀ x y : G,
    cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

/-- The ordinary undirected Cayley-CI defect predicate for a pointed
presentation. -/
def ordinaryCayleyCIDefect {G : Type*} [Group G]
    (f : Equiv.Perm G) (S T : Set G) : Prop :=
  cayleyGraphIsomorphism f S T ∧
    ¬ ∃ α : G ≃* G, Set.image (fun x => α x) S = T

/-- A difference cover written without relying on a particular set-product
notation: every group element is a quotient of two fixed points. -/
def isDifferenceCover {G : Type*} [Group G]
    (F : Set G) : Prop :=
  ∀ g : G, ∃ x ∈ F, ∃ y ∈ F, x⁻¹ * y = g

/-- The automorphism-normalized permutation in the theorem. -/
def normalizedPermutation {G : Type*} [Group G]
    (α : G ≃* G) (f : Equiv.Perm G) : G → G :=
  fun x => α.symm (f x)

/-- The source and target sets have the identity shadow. -/
def identityComponentShadow {G : Type*} [Group G] [DecidableEq G]
    (f : Equiv.Perm G) : Prop :=
  ∀ 𝒦 : Set (Set (IncidenceVertex G)),
    isComponentCollection f 𝒦 →
      cayleyGraphIsomorphism f (selectedSourceSet f 𝒦)
        (selectedTargetSet f 𝒦) ∧
      selectedSourceSet f 𝒦 = selectedTargetSet f 𝒦

/--
The fixed-difference-cover component-shadow theorem.  The automorphism is
quantified before the component collection, so the same `α` shadows every
selected union.  The second conjunct records the finite abelian direct-sum
specialization and its identity shadow.
-/
def fixedDifferenceCoverComponentShadow : Prop :=
  (∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
      (α : G ≃* G) (f : Equiv.Perm G),
    f 1 = 1 →
      isDifferenceCover
        {x : G | normalizedPermutation α f x = x} →
      (∀ C : Set (IncidenceVertex G),
        isIncidenceComponent f C →
          targetLabels f C = atomImageSet α (sourceLabels f C)) ∧
      (∀ 𝒦 : Set (Set (IncidenceVertex G)),
        isComponentCollection f 𝒦 →
          cayleyGraphIsomorphism f (selectedSourceSet f 𝒦)
            (selectedTargetSet f 𝒦) ∧
          Set.image (fun x => α x) (selectedSourceSet f 𝒦) =
            selectedTargetSet f 𝒦 ∧
          ¬ ordinaryCayleyCIDefect f
            (selectedSourceSet f 𝒦) (selectedTargetSet f 𝒦))) ∧
  (∀ (H K : Type*) [CommGroup H] [Fintype H] [DecidableEq H]
      [CommGroup K] [Fintype K] [DecidableEq K]
      (q : Equiv.Perm (H × K)),
    q (1, 1) = (1, 1) →
      (∀ h : H, q (h, 1) = (h, 1)) →
      (∀ k : K, q (1, k) = (1, k)) →
      isDifferenceCover {x : H × K | q x = x} ∧
        identityComponentShadow q)

end

end MathlibPlus.Open.GraphTheory.Claim61027
