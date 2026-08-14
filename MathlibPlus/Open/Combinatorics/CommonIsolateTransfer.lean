import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

noncomputable section

/-- Isomorphism of simple graphs on the same finite labelled vertex set size. -/
private def graphIso {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)

/-- The card obtained by deleting a specified vertex from a graph on `Fin (n+1)`. -/
private def deleteVertex {n : ℕ} (X : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    SimpleGraph (Fin n) :=
  X.comap (Fin.succAbove v)

/-- Add one isolated vertex, using the last vertex of the finite ordinal. -/
private def addIsolated {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun v w =>
    ∃ hv : v.val < n, ∃ hw : w.val < n,
      G.Adj ⟨v.val, hv⟩ ⟨w.val, hw⟩)

/-- Number of deletions of `X` that produce the graph class `F`. -/
private noncomputable def cardMultiplicity {n : ℕ}
    (F : SimpleGraph (Fin n)) (X : SimpleGraph (Fin (n + 1))) : ℕ := by
  classical
  exact ∑ v : Fin (n + 1), if graphIso F (deleteVertex X v) then 1 else 0

private noncomputable def graphIndicator {n : ℕ}
    (G H : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact if graphIso G H then 1 else 0

/-- The fixed-left linear/falling-pair row from Claim 22863. -/
private noncomputable def fixedLeftRow {n : ℕ}
    (F H : SimpleGraph (Fin n)) (X : SimpleGraph (Fin (n + 1))) : ℕ := by
  classical
  exact if graphIso F H then
    cardMultiplicity F X * (cardMultiplicity F X - 1)
  else
    cardMultiplicity F X * cardMultiplicity H X

/-- Claim 22863: exact common-isolate transfer identity. -/
def exactCommonIsolateTransferIdentity_22863 : Prop :=
  ∀ (m : ℕ) (F H : SimpleGraph (Fin m)) (X : SimpleGraph (Fin (m + 1))),
    fixedLeftRow (addIsolated F) (addIsolated H) (addIsolated X) =
      fixedLeftRow F H X
        + cardMultiplicity F X * graphIndicator X (addIsolated H)
        + graphIndicator X (addIsolated F) *
            (cardMultiplicity H X - graphIndicator F H)
        + graphIndicator X (addIsolated F) * graphIndicator X (addIsolated H)

end

end MathlibPlus.Open.Combinatorics
