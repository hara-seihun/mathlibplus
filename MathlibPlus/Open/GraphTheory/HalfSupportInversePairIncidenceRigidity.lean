import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

/-- A label for an inverse-pair atom `[d] = {d,-d}` with `d ≠ 0`. -/
def inversePairAtom (G : Type*) [AddCommGroup G] : Type _ := by
  classical
  exact {D : Finset G // ∃ d : G, d ≠ 0 ∧ D = {d, -d}}

/-- The directions carried by an inverse-pair atom label. -/
def inversePairAtomDirections {G : Type*} [AddCommGroup G]
    (D : inversePairAtom G) : Set G :=
  (D.1 : Set G)

/-- The unordered translation edges of an inverse-pair atom. -/
def inversePairTranslationEdges {G : Type*} [AddCommGroup G]
    (D : inversePairAtom G) : Set (Finset G) := by
  classical
  exact {e | ∃ d ∈ D.1, ∃ x : G, e = {x, x + d}}

/-- The image of an unordered edge under a vertex permutation. -/
def inversePairEdgeImage {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (e : Finset G) : Finset G := by
  classical
  exact e.image f

/-- The image of a set of unordered edges under a vertex permutation. -/
def inversePairEdgeSetImage {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (E : Set (Finset G)) : Set (Finset G) :=
  inversePairEdgeImage f '' E

/-- The two copies of the inverse-pair atom labels in the incidence graph. -/
def inversePairIncidenceVertex (G : Type*) [AddCommGroup G] : Type _ :=
  Sum (inversePairAtom G) (inversePairAtom G)

/-- Adjacency in the bipartite inverse-pair incidence graph. -/
def inversePairIncidenceAdjacency
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (u v : inversePairIncidenceVertex G) : Prop :=
  match u, v with
  | Sum.inl D, Sum.inr D' =>
      (inversePairEdgeSetImage f (inversePairTranslationEdges D) ∩
        inversePairTranslationEdges D').Nonempty
  | Sum.inr D', Sum.inl D =>
      (inversePairEdgeSetImage f (inversePairTranslationEdges D) ∩
        inversePairTranslationEdges D').Nonempty
  | _, _ => False

/-- Connectivity in the bipartite incidence graph. -/
def inversePairIncidenceConnected
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (u v : inversePairIncidenceVertex G) : Prop :=
  Relation.ReflTransGen (inversePairIncidenceAdjacency f) u v

/-- The source atom labels in the component containing a vertex. -/
def inversePairComponentSourceLabels
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (u : inversePairIncidenceVertex G) : Set (inversePairAtom G) :=
  {D | inversePairIncidenceConnected f u (Sum.inl D)}

/-- The target atom labels in the component containing a vertex. -/
def inversePairComponentTargetLabels
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (u : inversePairIncidenceVertex G) : Set (inversePairAtom G) :=
  {D | inversePairIncidenceConnected f u (Sum.inr D)}

/-- Every incidence component has the same source and target atom labels. -/
def inversePairIncidenceComponentsHaveMatchingLabels
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) : Prop :=
  ∀ u : inversePairIncidenceVertex G,
    inversePairComponentSourceLabels f u =
      inversePairComponentTargetLabels f u

/-- A set of incidence vertices that is a union of whole connected components. -/
def inversePairIncidenceComponentUnion
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (I : Set (inversePairIncidenceVertex G)) : Prop :=
  ∀ u v : inversePairIncidenceVertex G,
    inversePairIncidenceConnected f u v →
      (u ∈ I ↔ v ∈ I)

/-- The atom labels selected on the source side of a component union. -/
def inversePairSourceAtomUnion
    {G : Type*} [AddCommGroup G]
    (I : Set (inversePairIncidenceVertex G)) : Set (inversePairAtom G) :=
  {D | Sum.inl D ∈ I}

/-- The atom labels selected on the target side of a component union. -/
def inversePairTargetAtomUnion
    {G : Type*} [AddCommGroup G]
    (I : Set (inversePairIncidenceVertex G)) : Set (inversePairAtom G) :=
  {D | Sum.inr D ∈ I}

/-- The union of the directions carried by a set of inverse-pair atoms. -/
def inversePairConnectionSetOfAtoms
    {G : Type*} [AddCommGroup G]
    (A : Set (inversePairAtom G)) : Set G := by
  classical
  exact {d | ∃ D, D ∈ A ∧ d ∈ inversePairAtomDirections D}

/-- The source connection set of a union of incidence components. -/
def inversePairSourceConnectionSet
    {G : Type*} [AddCommGroup G]
    (I : Set (inversePairIncidenceVertex G)) : Set G :=
  inversePairConnectionSetOfAtoms (inversePairSourceAtomUnion I)

/-- The target connection set of a union of incidence components. -/
def inversePairTargetConnectionSet
    {G : Type*} [AddCommGroup G]
    (I : Set (inversePairIncidenceVertex G)) : Set G :=
  inversePairConnectionSetOfAtoms (inversePairTargetAtomUnion I)

/-- The union of all unordered edges belonging to a set of atom labels. -/
def inversePairEdgeUnionOfAtoms
    {G : Type*} [AddCommGroup G]
    (A : Set (inversePairAtom G)) : Set (Finset G) :=
  {e | ∃ D, D ∈ A ∧ e ∈ inversePairTranslationEdges D}

/-- The exact edge-level transport from source atoms to target atoms. -/
def inversePairCarriesEdgeUnion
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (A B : Set (inversePairAtom G)) : Prop :=
  ∀ e : Finset G,
    e ∈ inversePairEdgeUnionOfAtoms A ↔
      inversePairEdgeImage f e ∈ inversePairEdgeUnionOfAtoms B

/-- The identity-free inverse-closed condition for an additive connection set. -/
def inversePairIdentityFreeInverseClosed
    {G : Type*} [AddCommGroup G]
    (S : Set G) : Prop :=
  S ⊆ ({0} : Set G)ᶜ ∧ ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

/-- The additive Cayley relation carried by a connection set. -/
def inversePairCayleyRelation
    {G : Type*} [AddCommGroup G]
    (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

/-- A permutation carrying one additive Cayley relation to another. -/
def inversePairCarriesCayleyRelation
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G) (S T : Set G) : Prop :=
  ∀ x y : G,
    inversePairCayleyRelation S x y ↔
      inversePairCayleyRelation T (f x) (f y)

/-- A component-union Cayley defect: the carried relation has no group-automorphism shadow. -/
def inversePairOrdinaryCayleyCIDefect
    {G : Type*} [AddCommGroup G]
    (f : Equiv.Perm G)
    (I : Set (inversePairIncidenceVertex G)) : Prop :=
  inversePairIncidenceComponentUnion f I ∧
    inversePairIdentityFreeInverseClosed (inversePairSourceConnectionSet I) ∧
    inversePairIdentityFreeInverseClosed (inversePairTargetConnectionSet I) ∧
    inversePairCarriesCayleyRelation f
      (inversePairSourceConnectionSet I)
      (inversePairTargetConnectionSet I) ∧
    ¬ ∃ α : G ≃+ G,
      α '' inversePairSourceConnectionSet I =
        inversePairTargetConnectionSet I

/-- The support of a vertex permutation. -/
def inversePairPermutationSupport
    {G : Type*} [Fintype G]
    (f : Equiv.Perm G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => f x ≠ x)

/-- Moving strictly fewer than half of the finite group elements. -/
def inversePairSupportBelowHalf
    {G : Type*} [Fintype G]
    (f : Equiv.Perm G) : Prop :=
  2 * (inversePairPermutationSupport f).card < Fintype.card G

/-- Moving at least half of the finite group elements. -/
def inversePairSupportAtLeastHalf
    {G : Type*} [Fintype G]
    (f : Equiv.Perm G) : Prop :=
  Fintype.card G ≤ 2 * (inversePairPermutationSupport f).card

/-- Claim 61018: pointed permutations of support below half force diagonal
incidence labels, so every component union is shadowed by the identity Cayley
relation; a non-shadowed component attack therefore has support at least half. -/
def halfSupportInversePairIncidenceRigidity_claim61018 : Prop :=
  ∀ (G : Type*) [AddCommGroup G] [Fintype G]
    (f : Equiv.Perm G),
    f 0 = 0 →
      (inversePairSupportBelowHalf f →
        inversePairIncidenceComponentsHaveMatchingLabels f ∧
          ∀ I : Set (inversePairIncidenceVertex G),
            inversePairIncidenceComponentUnion f I →
              inversePairIdentityFreeInverseClosed
                  (inversePairSourceConnectionSet I) ∧
                inversePairIdentityFreeInverseClosed
                  (inversePairTargetConnectionSet I) ∧
                inversePairSourceConnectionSet I =
                  inversePairTargetConnectionSet I ∧
                inversePairCarriesEdgeUnion f
                  (inversePairSourceAtomUnion I)
                  (inversePairTargetAtomUnion I) ∧
                inversePairCarriesCayleyRelation f
                  (inversePairSourceConnectionSet I)
                  (inversePairTargetConnectionSet I) ∧
                inversePairCarriesCayleyRelation f
                  (inversePairSourceConnectionSet I)
                  (inversePairSourceConnectionSet I)) ∧
      ∀ I : Set (inversePairIncidenceVertex G),
        inversePairOrdinaryCayleyCIDefect f I →
          inversePairSupportAtLeastHalf f

end

end MathlibPlus.Open.GraphTheory
