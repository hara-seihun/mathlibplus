import MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386

namespace MathlibPlus.Open.ResearchFormalizationPseudosimilarity

/-- A base graph has minimum degree at least two when every vertex has two
  distinct neighbors. -/
def minimumDegreeAtLeastTwo {V : Type*} (C : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ u w : V, u ≠ w ∧ C.Adj v u ∧ C.Adj v w

/-- The graph obtained by adjoining one new vertex, `none`, adjacent only to
  the specified base vertex. -/
def attachPendant {V : Type*} (C : SimpleGraph V) (z : V) :
    SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | none, none => False
    | none, some v => v = z
    | some u, none => u = z
    | some u, some v => C.Adj u v
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact False.elim h
    · exact h
    · exact h
    · exact C.symm.symm _ _ h
  loopless := by
    constructor
    intro x h
    cases x with
    | none => exact False.elim h
    | some v => exact C.loopless.irrefl v h

/-- A vertex has degree one when it has exactly one neighbor. -/
def hasDegreeOne {W : Type*} (G : SimpleGraph W) (v : W) : Prop :=
  ∃ w : W, G.Adj v w ∧ ∀ u : W, G.Adj v u → u = w

/-- Claim 14318: under minimum degree two, pseudosimilar attachment vertices
  force the pendant vertex and its attachment to be transported, so any
  extension isomorphism restricts to a base automorphism; hence the two
  pendant extensions are non-isomorphic. -/
def claim14318_uniquePendantForcesNonisomorphism : Prop :=
  ∀ {V : Type*} (C : SimpleGraph V) (z z' : V),
    minimumDegreeAtLeastTwo C →
    MathlibPlus.Open.ResearchFormalizationLargeBatch01a00386.claim14314_pseudosimilar
      C z z' →
    (∀ v : Option V,
        hasDegreeOne (attachPendant C z) v ↔ v = none) ∧
      (∀ v : Option V,
        hasDegreeOne (attachPendant C z') v ↔ v = none) ∧
      (∀ e : SimpleGraph.Iso (attachPendant C z) (attachPendant C z'),
        e.toEquiv none = none ∧
          e.toEquiv (some z) = some z' ∧
          ∃ eC : SimpleGraph.Iso C C,
            eC.toEquiv z = z' ∧
              ∀ v : V,
                e.toEquiv (some v) = some (eC.toEquiv v)) ∧
      ¬ Nonempty (SimpleGraph.Iso (attachPendant C z)
        (attachPendant C z'))

end MathlibPlus.Open.ResearchFormalizationPseudosimilarity
