import Mathlib

namespace MathlibPlus.Open.Graphs.PrimeCycleTypeCounts9145

noncomputable section

open scoped BigOperators

private abbrev Vertex := Fin 24

private def graphSetoid : Setoid (SimpleGraph Vertex) :=
  { r := fun G H => Nonempty (G ≃g H)
    iseqv :=
      { refl := fun G => ⟨SimpleGraph.Iso.refl⟩
        symm := by
          intro G H h
          rcases h with ⟨e⟩
          exact ⟨e.symm⟩
        trans := by
          intro G H K hGH hHK
          rcases hGH with ⟨e⟩
          rcases hHK with ⟨f⟩
          exact ⟨f.comp e⟩ } }

private abbrev GraphClass := Quotient graphSetoid

private noncomputable def representative (C : GraphClass) : SimpleGraph Vertex :=
  Quotient.out C

private def hasCliqueOfSize (G : SimpleGraph Vertex) (n : Nat) : Prop :=
  ∃ s : Finset Vertex, s.card = n ∧ G.IsClique (s : Set Vertex)

private def hasIndependentSetOfSize (G : SimpleGraph Vertex) (n : Nat) : Prop :=
  ∃ s : Finset Vertex, s.card = n ∧
    (s : Set Vertex).Pairwise (fun x y => ¬G.Adj x y)

private def admissibleGraph (G : SimpleGraph Vertex) : Prop :=
  ¬hasCliqueOfSize G 4 ∧ ¬hasIndependentSetOfSize G 5

private def admissibleClass (C : GraphClass) : Prop :=
  admissibleGraph (representative C)

private noncomputable instance graphClassFintype : Fintype GraphClass :=
  Fintype.ofFinite GraphClass

private noncomputable def admissibleClasses : Finset GraphClass := by
  classical
  exact Finset.filter admissibleClass Finset.univ

private def GraphAutomorphism (G : SimpleGraph Vertex) :=
  {σ : Equiv.Perm Vertex // ∀ x y : Vertex, G.Adj x y ↔ G.Adj (σ x) (σ y)}

private noncomputable instance graphAutomorphismFintype
    (G : SimpleGraph Vertex) : Fintype (GraphAutomorphism G) :=
  Fintype.ofInjective (fun σ : GraphAutomorphism G => σ.1)
    (fun σ τ h => Subtype.ext h)

private noncomputable def fixedPointCount (σ : Equiv.Perm Vertex) : Nat := by
  classical
  exact (Finset.univ.filter (fun x => σ x = x)).card

private def hasPrimeCycleType (G : SimpleGraph Vertex) (p cycles fixed : Nat)
    (σ : GraphAutomorphism G) : Prop :=
  Nat.Prime p ∧ orderOf σ.1 = p ∧
    (σ.1.cycleType.count p = cycles) ∧
    (fixedPointCount σ.1 = fixed)

private noncomputable def automorphismsOfType (C : GraphClass)
    (p cycles fixed : Nat) : Finset (GraphAutomorphism (representative C)) := by
  classical
  exact Finset.filter
    (hasPrimeCycleType (representative C) p cycles fixed) Finset.univ

private noncomputable def graphAndElementCounts (p cycles fixed : Nat) : Nat × Nat := by
  classical
  exact ((admissibleClasses.filter
      (fun C => ∃ σ, hasPrimeCycleType (representative C) p cycles fixed σ)).card,
    admissibleClasses.sum (fun C => (automorphismsOfType C p cycles fixed).card))

def exactGraphAndElementCountsByPrimeCycleType : Prop :=
  graphAndElementCounts 2 8 8 = (16, 19) ∧
  graphAndElementCounts 2 9 6 = (980, 985) ∧
  graphAndElementCounts 2 10 4 = (1363, 1493) ∧
  graphAndElementCounts 2 11 2 = (923, 971) ∧
  graphAndElementCounts 2 12 0 = (8201, 9016) ∧
  graphAndElementCounts 3 7 3 = (1, 4) ∧
  graphAndElementCounts 3 8 0 = (69, 146)

end
end MathlibPlus.Open.Graphs.PrimeCycleTypeCounts9145
