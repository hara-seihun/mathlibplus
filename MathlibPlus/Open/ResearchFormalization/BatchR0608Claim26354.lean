import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchR0608Claim26354

attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev AlphabetPolynomial := MvPolynomial ℕ ℚ

private abbrev ProperColoring {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset ℕ) :=
  {c : V → {a // a ∈ A} //
    ∀ v w : V, G.Adj v w → c v ≠ c w}

private noncomputable def properColoringFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset ℕ) : Fintype (ProperColoring G A) :=
  Fintype.ofFinite _

private noncomputable def chromaticFunctionOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset ℕ) : AlphabetPolynomial :=
  letI := properColoringFintype G A
  ∑ c : ProperColoring G A,
    ∏ v : V, MvPolynomial.X (c.1 v).1

private def deletedGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  G.induce {v : V | v ∉ S}

private def inducedGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce (S : Set V)

private def rootedTwoAlphabetChromatic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ) : AlphabetPolynomial :=
  ∑ S ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ r)).powerset,
    chromaticFunctionOn (deletedGraph G S) A *
      chromaticFunctionOn (inducedGraph G S) B

/-- The two root orientations are the two disjoint-alphabet pieces of the
ordinary finite-alphabet chromatic symmetric function. -/
def orientedForgetfulSplit_claim26354 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (A B : Finset ℕ),
    Disjoint A B →
      rootedTwoAlphabetChromatic G r A B +
          rootedTwoAlphabetChromatic G r B A =
        chromaticFunctionOn G (A ∪ B)

end MathlibPlus.Open.ResearchFormalization.BatchR0608Claim26354
