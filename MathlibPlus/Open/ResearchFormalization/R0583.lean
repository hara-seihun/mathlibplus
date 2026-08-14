import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0583

/-- The edge relation of a corolla on pairwise-disjoint, tagged branch carriers. -/
def rootedCorollaEdgeLaw {ι : Type*} {V : ι → Type*}
    (G : (i : ι) → SimpleGraph (V i)) (r : (i : ι) → V i)
    (B : SimpleGraph (Option (Σ i, V i))) : Prop :=
  ∀ x y, B.Adj x y ↔
    x ≠ y ∧
      ((x = none ∧ ∃ i, y = some ⟨i, r i⟩) ∨
        (y = none ∧ ∃ i, x = some ⟨i, r i⟩) ∨
        ∃ i v w, x = some ⟨i, v⟩ ∧ y = some ⟨i, w⟩ ∧ (G i).Adj v w)

def emptyBranchType : Empty → Type := fun i => nomatch i

def emptyBranchGraph : (i : Empty) → SimpleGraph (emptyBranchType i) :=
  fun i => nomatch i

def emptyBranchRoot : (i : Empty) → emptyBranchType i :=
  fun i => nomatch i

def rootedSingletonGraph : SimpleGraph (Option (Σ i : Empty, emptyBranchType i)) := ⊥

/--
The exact rooted-corolla grafting claim: the new vertex is `none`, each old
carrier is tagged by its branch index, and the zero-branch case is the pointed
singleton (the bottom graph with distinguished root `none`).
-/
def rootedCorollaGrafting_22978 : Prop :=
  (∀ (ι : Type*) [Fintype ι] (V : ι → Type*) [∀ i, Fintype (V i)]
      (G : (i : ι) → SimpleGraph (V i)) (r : (i : ι) → V i),
    ∃! B : SimpleGraph (Option (Σ i, V i)), rootedCorollaEdgeLaw G r B) ∧
    rootedCorollaEdgeLaw emptyBranchGraph emptyBranchRoot rootedSingletonGraph

end MathlibPlus.Open.ResearchFormalization.R0583
