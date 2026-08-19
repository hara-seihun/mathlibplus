import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0608Claim26353

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev TwoAlphabetSymmetricCarrier26353 := MvPolynomial ℕ ℚ

def properColoring26353 {V : Type*} (G : SimpleGraph V)
    (c : V → ℕ) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

def coloringWeight26353 {V : Type*} [Fintype V]
    (c : V → ℕ) : TwoAlphabetSymmetricCarrier26353 :=
  ∏ v : V, MvPolynomial.X (c v)

def deletedGraph26353 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  G.induce {v : V | v ∉ S}

def inducedGraph26353 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce (S : Set V)

def finiteAlphabetChromatic26353
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset ℕ) : TwoAlphabetSymmetricCarrier26353 :=
  ∑ c : V → A,
    if properColoring26353 G (fun v => (c v).1) then
      coloringWeight26353 (fun v => (c v).1)
    else 0

def rootedTwoAlphabetChromatic26353
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ) :
    TwoAlphabetSymmetricCarrier26353 :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    finiteAlphabetChromatic26353 (deletedGraph26353 G S) A *
      finiteAlphabetChromatic26353 (inducedGraph26353 G S) B

def rootedAProperColoringGenerating26353
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ) :
    TwoAlphabetSymmetricCarrier26353 :=
  ∑ c : V → (↥(A ∪ B)),
    if properColoring26353 G (fun v => (c v).1) ∧ (c r).1 ∈ A then
      coloringWeight26353 (fun v => (c v).1)
    else 0

/-- Claim 26353: the rooted subset convolution is the weighted proper-coloring
sum on the disjoint union of the two finite alphabets, with the root on A. -/
def claim26353 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ),
    Disjoint A B →
      rootedTwoAlphabetChromatic26353 G r A B =
        rootedAProperColoringGenerating26353 G r A B

end

end MathlibPlus.Open.ResearchFormalization.R0608Claim26353
