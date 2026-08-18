import MathlibPlus.Open.ResearchFormalization.R0330Claim19947

namespace MathlibPlus.Open.ResearchFormalization.R0330Claim19932

noncomputable section
open Classical
open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0330Claim19947

/-- The first x-variable in an m-colour deck, with its index made explicit
for the source's hypothesis that m is positive. -/
def firstIndex {m : ℕ} (hm : 1 ≤ m) : Fin m :=
  Fin.cast (Nat.sub_add_cancel hm) (0 : Fin (m - 1 + 1))

/-- The variable shift which embeds the remaining m-1 colour variables after
colour one. -/
def shiftVarAt {m : ℕ} (hm : 1 ≤ m) : DeckVar (m - 1) → DeckVar m
  | Sum.inl i => Sum.inl (Fin.cast (Nat.sub_add_cancel hm) (Fin.succ i))
  | Sum.inr (Sum.inl i) =>
      Sum.inr (Sum.inl (Fin.cast (Nat.sub_add_cancel hm) (Fin.succ i)))
  | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr u)

/-- Coefficient extraction in the first x-variable of an m-colour deck. -/
def firstXCoefficient {V : Type} [Fintype V]
    {m : ℕ} (hm : 1 ≤ m) (p : DeckPolynomial V m) (a : ℕ) :
    DeckPolynomial V m :=
  variableCoefficient p (xVar m (firstIndex hm)) a

/-- The exact induced-subgraph deletion layer for an arbitrary positive number
of colours. -/
def firstInducedLayer {V : Type} [Fintype V]
    (F : SimpleGraph V) {m : ℕ} (hm : 1 ≤ m) (a : ℕ) :
    DeckPolynomial V m :=
  ∑ A : Finset V,
    if A.card = a then
      (MvPolynomial.X (zVar m (firstIndex hm)) ^ internalEdgeCount F A) *
        (MvPolynomial.X (yVar m) ^ crossingEdgeCount F A) *
        MvPolynomial.rename (shiftVarAt hm : DeckVar (m - 1) → DeckVar m)
          (deckInvariant (deletedGraph F A) (m - 1))
    else 0

/-- Claim 19932: extracting x₁^a from the m-colour invariant is the exact
sum over a-vertex induced deletions, with internal, crossing, and recursively
coloured-deleted-forest weights. -/
def claim19932 : Prop :=
  ∀ {V : Type} [Fintype V] (F : SimpleGraph V), SimpleGraph.IsAcyclic F →
    ∀ (m : ℕ) (hm : 1 ≤ m), ∀ a : ℕ,
      firstXCoefficient hm (deckInvariant F m) a =
        firstInducedLayer F hm a

end

end MathlibPlus.Open.ResearchFormalization.R0330Claim19932
