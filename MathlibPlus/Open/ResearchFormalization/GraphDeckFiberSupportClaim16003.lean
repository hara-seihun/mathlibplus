import Mathlib
import MathlibPlus.Combinatorics.Claim44521

namespace MathlibPlus.Open.ResearchFormalization.Claim16003

noncomputable section

private abbrev GraphType (n : ℕ) :=
  MathlibPlus.Combinatorics.Claim44521.finiteSimpleGraphType n

private def graphRepresentative {n : ℕ} (G : GraphType n) : SimpleGraph (Fin n) :=
  Quotient.out G

private def deletedVertexGraph {m : ℕ} (G : SimpleGraph (Fin (m + 1)))
    (v : Fin (m + 1)) : SimpleGraph (Fin m) :=
  G.comap v.succAbove

private def cardMultiplicity (F : GraphType m) (G : GraphType (m + 1)) : ℕ :=
  Nat.card {v : Fin (m + 1) //
    MathlibPlus.Combinatorics.Claim44521.graphTypeOf m
      (deletedVertexGraph (graphRepresentative G) v) = F}

private def fallingCardRow (F H : GraphType m) : GraphType (m + 1) → ℚ :=
  letI : DecidableEq (GraphType m) := Classical.decEq _
  fun G =>
    if F = H then
      (cardMultiplicity F G : ℚ) *
        ((cardMultiplicity F G - 1 : ℕ) : ℚ)
    else
      (cardMultiplicity F G : ℚ) * (cardMultiplicity H G : ℚ)

private def extensionFiber (F : GraphType m) : Set (GraphType (m + 1)) :=
  {G | 0 < cardMultiplicity F G}

/-- Claim 16003: every falling quadratic deck row indexed by `F,H` has
support contained in the extension fibre of `F`, defined by the positive
multiplicity condition `d_F(G) > 0`. -/
def claim16003 : Prop :=
  ∀ (m : ℕ) (F H : GraphType m),
    Function.support (fallingCardRow F H) ⊆ extensionFiber F

end
end MathlibPlus.Open.ResearchFormalization.Claim16003
