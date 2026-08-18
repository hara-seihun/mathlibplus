import MathlibPlus.Open.ResearchFormalization.R0330Claim19947

namespace MathlibPlus.Open.ResearchFormalization.R0330Claim19933

noncomputable section
open Classical
open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0330Claim19947

/-- One induced-subgraph deck step. The input J is a recursively coloured
invariant on the deleted graph, and the rename places its variables after the
new first colour. -/
def deckOperator {V : Type} [Fintype V] (m : ℕ)
    (J : ∀ {W : Type} [Fintype W], SimpleGraph W → DeckPolynomial W m)
    (F : SimpleGraph V) : DeckPolynomial V (m + 1) :=
  ∑ A : Finset V,
    (MvPolynomial.X (xVar (m + 1) 0) ^ A.card) *
      (MvPolynomial.X (zVar (m + 1) 0) ^ internalEdgeCount F A) *
      (MvPolynomial.X (yVar (m + 1)) ^ crossingEdgeCount F A) *
      MvPolynomial.rename (shiftVar : DeckVar m → DeckVar (m + 1))
        (J (deletedGraph F A))

/-- Iteration of the induced-subgraph deck operator from the constant
function 1. -/
def iteratedDeckTransform (m : ℕ) {V : Type} [Fintype V]
    (F : SimpleGraph V) : DeckPolynomial V m :=
  match m with
  | 0 => 1
  | m + 1 =>
      deckOperator m
        (fun {W : Type} [Fintype W] (G : SimpleGraph W) =>
          iteratedDeckTransform m G)
        F

/-- Claim 19933: the recursively coloured forest invariant is the m-fold
induced-subgraph deck transform of the constant function 1. -/
def claim19933 : Prop :=
  ∀ {V : Type} [Fintype V] (F : SimpleGraph V),
    ∀ m : ℕ, deckInvariant F m = iteratedDeckTransform m F

end

end MathlibPlus.Open.ResearchFormalization.R0330Claim19933
