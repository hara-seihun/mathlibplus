import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_019ffedf

/-- One oriented step in the cyclic quotient. -/
def cycleStep (j : ℕ) (i k : Fin j) : Prop :=
  (i.val + 1) % j = k.val

/-- Blow up every cyclic quotient part to an independent set of the prescribed size. -/
def cycleBlowUp (j : ℕ) (partSize : Fin j → ℕ) :
    SimpleGraph (Σ i : Fin j, Fin (partSize i)) :=
  SimpleGraph.fromRel (fun v w => cycleStep j v.1 w.1)

/-- The uniform cycle blow-up `C_j[\overline{K_n}]`. -/
def rccHost (n j : ℕ) : SimpleGraph (Σ i : Fin j, Fin n) :=
  cycleBlowUp j (fun _ => n)

/-- The cycle blow-up with one part of size `n - 1` and all remaining parts of size `n`. -/
def rccSoleCard (n j : ℕ) :
    SimpleGraph (Σ i : Fin j, Fin (if i.val = 0 then n - 1 else n)) :=
  cycleBlowUp j (fun i => if i.val = 0 then n - 1 else n)

/-- The vertex-deletion card of a simple graph. -/
def vertexDelete {V : Type} (G : SimpleGraph V) (x : V) :
    SimpleGraph {v : V // v ≠ x} :=
  G.induce {v : V | v ≠ x}

/-- Isomorphism of simple graphs, regarded as a proposition rather than a
choice of a particular isomorphism. -/
def graphIsomorphic {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Nonempty (G ≃g H)

/-- The unit-transfer part-size vector and its cycle blow-up. -/
def unitTransferPartSize {j : ℕ} (n : ℕ) (r i : Fin j) : ℕ :=
  if i.val = 0 then n - 1 else if i = r then n + 1 else n

def unitTransferGraph {j : ℕ} (n : ℕ) (r : Fin j) :
    SimpleGraph (Σ i : Fin j, Fin (unitTransferPartSize n r i)) :=
  cycleBlowUp j (unitTransferPartSize n r)

/-- Having three distinct vertex-deletion cards isomorphic to a fixed graph. -/
def hasThreeCards {V W : Type} [Fintype V]
    (X : SimpleGraph V) (A : SimpleGraph W) : Prop :=
  ∃ x y z : V,
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    graphIsomorphic (vertexDelete X x) A ∧
    graphIsomorphic (vertexDelete X y) A ∧
    graphIsomorphic (vertexDelete X z) A

/-- Claim 23804: for `n ≥ 3` and `j ≥ 5`, every vertex-deletion card of
`RCC_{n,j}` is isomorphic to the one-part-deficient cycle blow-up. -/
def claim23804 : Prop :=
  ∀ n j : ℕ, 3 ≤ n → 5 ≤ j →
    ∀ x : Σ i : Fin j, Fin n,
      graphIsomorphic (vertexDelete (rccHost n j) x) (rccSoleCard n j)

/-- Claim 23808: the three-card parent classification for the RCC sole card. -/
def claim23808 : Prop :=
  ∀ n j : ℕ, 3 ≤ n → 5 ≤ j →
    ∀ {V : Type} [Fintype V] (X : SimpleGraph V),
      hasThreeCards X (rccSoleCard n j) →
      graphIsomorphic X (rccHost n j) ∨
        ∃ r : Fin j,
          1 ≤ r.val ∧ r.val ≤ j / 2 ∧
          graphIsomorphic X (unitTransferGraph n r)

end MathlibPlus.Open.ResearchFormalizationBatch_019ffedf
