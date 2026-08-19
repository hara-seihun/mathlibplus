import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1004LeafFiltration

open Classical

noncomputable section

/-- The finite degree count used by the all-tree P3-excess filtration. -/
noncomputable def graphDegree_claim29682
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The exact P3 excess `q(T)=Σ_v binom(deg_T(v)-1,2)`. -/
noncomputable def p3Excess_claim29682
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  ∑ w : V, Nat.choose (graphDegree_claim29682 G w - 1) 2

/-- The literal option-leaf attachment relation at a specified vertex. -/
def leafAttachmentRelation_claim29682
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (T : SimpleGraph (Option V)) (v : V) : Prop :=
  ∀ x y : Option V,
    T.Adj x y ↔
      match x, y with
      | some a, some b => C.Adj a b
      | none, some a => a = v
      | some a, none => a = v
      | none, none => False

/-- The leaf-extension carrier for the filtration statement. -/
def leafExtension_claim29682
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (T : SimpleGraph (Option V))
    (v : V) (d : ℕ) : Prop :=
  C.IsTree ∧ T.IsTree ∧
    graphDegree_claim29682 C v = d ∧
    leafAttachmentRelation_claim29682 C T v

/-- Attaching a leaf is monotone for the P3-excess filtration, with equality
exactly at a degree-one (pendant-arm) attachment. -/
def claim29682 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (T : SimpleGraph (Option V))
    (v : V) (d : ℕ),
    1 ≤ d →
    leafExtension_claim29682 C T v d →
    p3Excess_claim29682 T ≥ p3Excess_claim29682 C ∧
      (p3Excess_claim29682 T = p3Excess_claim29682 C ↔ d = 1)

end
end MathlibPlus.Open.ResearchFormalization.R1004LeafFiltration
