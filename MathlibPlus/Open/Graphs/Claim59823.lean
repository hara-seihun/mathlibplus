import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Graphs

noncomputable section

abbrev Vertex := Fin 8

private def graphTypeSetoid : Setoid (SimpleGraph Vertex) :=
  { r := fun G H => Nonempty (G ≃g H)
    iseqv :=
      { refl := fun G => ⟨SimpleGraph.Iso.refl⟩
        symm := fun {G H} h => by
          rcases h with ⟨e⟩
          exact ⟨e.symm⟩
        trans := fun {G H K} hGH hHK => by
          rcases hGH with ⟨eGH⟩
          rcases hHK with ⟨eHK⟩
          exact ⟨eGH.trans eHK⟩ } }

abbrev GraphType := Quotient graphTypeSetoid

instance : Fintype GraphType := Fintype.ofFinite GraphType

namespace GraphType

def representative (G : GraphType) : SimpleGraph Vertex := Quotient.out G

def edgeCount (G : GraphType) : ℕ := by
  letI := Fintype.ofFinite {e : Sym2 Vertex // e ∈ (representative G).edgeSet}
  exact Fintype.card {e : Sym2 Vertex // e ∈ (representative G).edgeSet}

def nonempty (G : GraphType) : Prop :=
  (representative G).edgeSet.Nonempty

def connected (G : GraphType) : Prop :=
  (representative G).Connected

def complementConnected (G : GraphType) : Prop :=
  (representative G)ᶜ.Connected

def admissible (G : GraphType) : Prop :=
  connected G ∧ complementConnected G

def sevenEdgeAdmissible (G : GraphType) : Prop :=
  edgeCount G = 7 ∧ admissible G

end GraphType

abbrev GraphVector := GraphType → ℚ

abbrev GraphRow :=
  {p : GraphType × GraphType //
    GraphType.edgeCount p.1 + GraphType.edgeCount p.2 = 7 ∧
      GraphType.nonempty p.1 ∧ GraphType.nonempty p.2}

abbrev RowVector := GraphRow → ℚ

def edgePartition (F₁ F₂ F : SimpleGraph Vertex) : Prop :=
  ∀ u v, F.Adj u v ↔
    (F₁.Adj u v ∨ F₂.Adj u v) ∧ ¬ (F₁.Adj u v ∧ F₂.Adj u v)

def graphIso (G H : SimpleGraph Vertex) : Prop := Nonempty (G ≃g H)
def partitionWitness (A B F : GraphType) (q : SimpleGraph Vertex × SimpleGraph Vertex) : Prop :=
  edgePartition q.1 q.2 (GraphType.representative F) ∧
    graphIso q.1 (GraphType.representative A) ∧
    graphIso q.2 (GraphType.representative B)

def partitionCount (A B F : GraphType) : ℕ := by
  letI := Fintype.ofFinite
    {q : SimpleGraph Vertex × SimpleGraph Vertex // partitionWitness A B F q}
  exact Fintype.card
    {q : SimpleGraph Vertex × SimpleGraph Vertex // partitionWitness A B F q}

def incidenceEntry (A B F : GraphType) : ℚ :=
  partitionCount A B F

def basisVector (F : GraphType) : GraphVector :=
  fun G => if G = F then 1 else 0

def admissibleSpan : Submodule ℚ GraphVector :=
  Submodule.span ℚ {v | ∃ F : GraphType, GraphType.sevenEdgeAdmissible F ∧ v = basisVector F}

def incidenceMap : GraphVector →ₗ[ℚ] RowVector :=
  { toFun := fun x r => ∑ F : GraphType, incidenceEntry r.1.1 r.1.2 F * x F
    map_add' := by
      intro x y
      funext r
      simp [Finset.sum_add_distrib, mul_add]
    map_smul' := by
      intro c x
      funext r
      change (∑ F : GraphType, incidenceEntry r.1.1 r.1.2 F * (c * x F)) =
        c * ∑ F : GraphType, incidenceEntry r.1.1 r.1.2 F * x F
      calc
        (∑ F : GraphType, incidenceEntry r.1.1 r.1.2 F * (c * x F)) =
            ∑ F : GraphType, c * (incidenceEntry r.1.1 r.1.2 F * x F) := by
              apply Finset.sum_congr rfl
              intro F hF
              ring
        _ = c * ∑ F : GraphType, incidenceEntry r.1.1 r.1.2 F * x F := by
              rw [Finset.mul_sum] }

def claim_59823 : Prop :=
  LinearMap.ker incidenceMap ⊓ admissibleSpan = ⊥

end
end MathlibPlus.Open.Graphs
