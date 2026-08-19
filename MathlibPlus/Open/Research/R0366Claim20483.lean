import Mathlib

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

namespace MathlibPlus.Open.Research.R0366Claim20483

abbrev Cell (r : ℕ) := Finset (Fin r)

def rootCell {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) (v : V) : Cell r :=
  Finset.univ.filter (fun i => G.Adj (x i) v)

def rootHasInternalGraph {V : Type*} {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) (A : SimpleGraph (Fin r)) : Prop :=
  Function.Injective x ∧
    ∀ i j : Fin r, A.Adj i j ↔ G.Adj (x i) (x j)

def rootMonomial {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) : MvPolynomial (Cell r) ℚ :=
  ∏ v : {v : V // v ∉ Set.range x},
    MvPolynomial.X (rootCell G x v.1)

def profilePolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (A : SimpleGraph (Fin r)) :
    MvPolynomial (Cell r) ℚ :=
  ∑ x : {x : Fin r → V // rootHasInternalGraph G x A},
    rootMonomial G x.1

def cardGraph {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph {u : V // u ≠ v} :=
  G.induce {u : V | u ≠ v}

def cardProfilePolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) {r : ℕ} (A : SimpleGraph (Fin r)) :
    MvPolynomial (Cell r) ℚ :=
  profilePolynomial (cardGraph G v) A

def cardDirectionalDerivative {r : ℕ}
    (p : MvPolynomial (Cell r) ℚ) : MvPolynomial (Cell r) ℚ :=
  ∑ S : Cell r, MvPolynomial.pderiv S p

def cardSumIsDirectionalDerivative20483 : Prop :=
  ∀ (n r : ℕ), 1 ≤ r → r < n →
    ∀ (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r)),
      (∑ v : Fin n, cardProfilePolynomial G v A) =
        cardDirectionalDerivative (profilePolynomial G A)

end MathlibPlus.Open.Research.R0366Claim20483
