import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.GraphDeckRowsClaim15999

open scoped BigOperators

noncomputable section

private def graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G H := Nonempty (G ≃g H)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro G
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro G H h
      exact h.map SimpleGraph.Iso.symm
    · intro G H K hGH hHK
      rcases hGH with ⟨f⟩
      rcases hHK with ⟨g⟩
      exact ⟨SimpleGraph.Iso.comp g f⟩

private abbrev GraphType (n : ℕ) := Quotient (graphIsoSetoid n)

private def graphRepresentative {n : ℕ} (G : GraphType n) : SimpleGraph (Fin n) :=
  Quotient.out G

private def deletedVertexGraph {m : ℕ} (G : SimpleGraph (Fin (m + 1)))
    (v : Fin (m + 1)) : SimpleGraph (Fin m) :=
  { Adj := fun i j => G.Adj (v.succAbove i) (v.succAbove j)
    symm := ⟨fun i j h => G.symm.symm _ _ h⟩
    loopless := ⟨fun i h => G.loopless.irrefl _ h⟩ }

private def cardMultiplicity (F : GraphType m) (G : GraphType (m + 1)) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (m + 1))).filter
    (fun v => Quotient.mk (graphIsoSetoid m)
      (deletedVertexGraph (graphRepresentative G) v) = F)).card

private def linearCardRow (F : GraphType m) : GraphType (m + 1) → ℚ :=
  fun G => (cardMultiplicity F G : ℚ)

private def quadraticCardRow (F H : GraphType m) : GraphType (m + 1) → ℚ := by
  classical
  exact fun G =>
    if F = H then
      (cardMultiplicity F G : ℚ) *
        ((cardMultiplicity F G - 1 : ℕ) : ℚ)
    else
      (cardMultiplicity F G : ℚ) * (cardMultiplicity H G : ℚ)

private def fallingQuadraticRowSpan (m : ℕ) :
    Submodule ℚ (GraphType (m + 1) → ℚ) :=
  Submodule.span ℚ (Set.range (fun FH : GraphType m × GraphType m =>
    quadraticCardRow FH.1 FH.2))

/-- Claim 15999: every linear card row is in the span of the complete
falling-quadratic row family, including distinct-card products and falling
squares. -/
def claim15999 : Prop :=
  ∀ (m : ℕ) (F : GraphType m),
    linearCardRow F ∈ fallingQuadraticRowSpan m

end

end MathlibPlus.Open.ResearchFormalization.GraphDeckRowsClaim15999
