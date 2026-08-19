import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.D0078Claim5066

noncomputable section

/-- The number of connected components of a finite simple graph. -/
noncomputable def componentCount {V : Type} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  Fintype.card G.ConnectedComponent

/-- The degree of a vertex in a finite simple graph. -/
noncomputable def finiteDegree {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  letI : Fintype (G.neighborSet v) := Fintype.ofFinite _
  G.degree v

/-- Claim 5066: deleting a vertex from a finite tree leaves exactly as many
connected components as the deleted vertex had neighbors. -/
def claim5066 : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)), T.IsTree →
    ∀ v : Fin n,
      componentCount (T.induce {w : Fin n | w ≠ v}) = finiteDegree T v

end
end MathlibPlus.Open.ResearchFormalization.D0078Claim5066
