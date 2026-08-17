import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Graphs.R0524

noncomputable section

/-- A nonempty vertex subset induces a connected set of the tree. -/
def connectedSet {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ (T.induce (↑S : Set V)).Connected

/-- The vertex carrier complementary to a finite set. -/
def outsideSet {V : Type*} [DecidableEq V]
    (S : Finset V) : Set V :=
  {v | v ∉ S}

/-- The forest obtained by deleting a finite vertex set. -/
def complementGraph {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ outsideSet S} :=
  T.induce (outsideSet S)

/-- The number of components of the deletion complement. -/
def complementComponents {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : ℕ :=
  Fintype.card (complementGraph T S).ConnectedComponent

/-- The degree polynomial of the components of the complement forest. -/
def complementDegreePolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Polynomial ℚ :=
  ∑ x : {v // v ∈ outsideSet S},
    Polynomial.X ^ (complementGraph T S).degree x

/-- The component count after deleting the connected set and one further
outside vertex. -/
def oneHoleComponents {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  Fintype.card
    (T.induce (outsideSet (S ∪ {x}))).ConnectedComponent

/-- The contribution of a fixed connected set to the one-hole transform. -/
def oneHoleContribution {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Polynomial ℚ :=
  ∑ x : {v // v ∈ outsideSet S},
    Polynomial.X ^ oneHoleComponents T S x.1

/-- For a finite tree, the one-hole contribution of a connected set is the
component-count weight times the degree polynomial of the complementary forest. -/
def claim_22345 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V),
    T.IsTree →
      connectedSet T S →
        oneHoleContribution T S =
          Polynomial.X ^ (complementComponents T S - 1) *
            complementDegreePolynomial T S

/-- The value and derivative identities for one connected-set contribution. -/
def claim_22346 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V),
    T.IsTree →
      connectedSet T S →
        let q := Fintype.card V - S.card
        let d := complementComponents T S
        Polynomial.eval (1 : ℚ) (complementDegreePolynomial T S) =
            (q : ℚ) ∧
          Polynomial.eval (1 : ℚ)
              (complementDegreePolynomial T S).derivative =
            2 * ((q - d : ℕ) : ℚ) ∧
          Polynomial.eval (1 : ℚ) (oneHoleContribution T S) =
            (q : ℚ) ∧
          Polynomial.eval (1 : ℚ)
              (oneHoleContribution T S).derivative =
            (q : ℚ) + ((q : ℚ) - 2) * (d : ℚ)

/-- The connected-set polynomial specialized at its boundary variable one. -/
def connectedSetPolynomialAtOne {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Polynomial ℚ :=
  ∑ S : Finset V,
    if connectedSet T S then Polynomial.X ^ S.card else 0

/-- The one-hole transform specialized at its component variable one. -/
def oneHoleTransformAtOne {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Polynomial ℚ :=
  ∑ S : Finset V,
    if connectedSet T S then
      ∑ x : {v // v ∈ outsideSet S}, Polynomial.X ^ S.card
    else 0

/-- Connected-set coefficients are recovered from the first one-hole layer,
with the full-tree coefficient fixed at one. -/
def claim_22347 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V),
    T.IsTree →
      let n := Fintype.card V
      (∀ m : ℕ, m < n →
        (connectedSetPolynomialAtOne T).coeff m =
          (oneHoleTransformAtOne T).coeff m / ((n - m : ℕ) : ℚ)) ∧
        (connectedSetPolynomialAtOne T).coeff n = 1

end

end MathlibPlus.Open.Graphs.R0524
