import MathlibPlus.Open.ResearchFormalization.R0335

namespace MathlibPlus.Open.ResearchFormalization.R0335.Claim20028

noncomputable section

open scoped BigOperators
open Classical
open MathlibPlus.Open.TreeSpectral
open MathlibPlus.Open.ResearchFormalization.R0335

/-- Ordered pairs of successive vertices for length-two walks whose second
endpoint does not return to the starting vertex. -/
private def nonbacktrackingTwoWalkCount {m : ℕ}
    (G : SimpleGraph (Fin m)) (v : Fin m) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => G.Adj v p.1 ∧ G.Adj p.1 p.2 ∧ p.2 ≠ v)).card

/-- Claim 20028: for a leaf `ell` of a target tree, any attachment neighbor
transported through a deletion isomorphism to the fixed card representative
has the exact two-step attachment weight as its length-two nonbacktracking
walk count in that card. -/
def claim20028 : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (C : TreeClass (n - 1)) (T : TreeClass n) (ell : Fin n),
      representativeIsLeaf T ell →
        cardDeletionIsomorphism C T ell →
          ∀ (v : {w : Fin n // w ≠ ell ∧ (Quotient.out T).1.Adj ell w}),
            ∀ (φ :
              (Quotient.out T).1.induce {w : Fin n | w ≠ ell} ≃g
                (Quotient.out C).1),
              nonbacktrackingTwoWalkCount (Quotient.out C).1
                  (φ ⟨v.1, v.2.1⟩) =
                attachmentTwoStepWeight T ell

end

end MathlibPlus.Open.ResearchFormalization.R0335.Claim20028
