import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchR0608Claim26351

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

private abbrev GraphCharacter (R : Type) [CommRing R] :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V], SimpleGraph V → R

private def chromaticCharacter (A : Finset ℕ) :
    GraphCharacter AlphabetPolynomial :=
  fun V _ _ G => chromaticFunctionOn G A

private def characterConvolution
    (a b : GraphCharacter AlphabetPolynomial) :
    GraphCharacter AlphabetPolynomial :=
  fun V _ _ G =>
    ∑ S : Finset V,
      a {v // v ∉ S} (G.induce {v | v ∉ S}) *
        b {v // v ∈ S} (G.induce (S : Set V))

/-- Claim 26351: finite-alphabet chromatic characters convolve by disjoint
alphabet addition; the character is proper-coloring polynomial evaluation and
convolution sums the two induced-graph factors over every vertex subset. -/
def chromaticCharactersConvolveByAlphabetAddition_claim26351 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset ℕ),
    Disjoint A B →
      characterConvolution (chromaticCharacter A) (chromaticCharacter B) V G =
        chromaticCharacter (A ∪ B) V G

end MathlibPlus.Open.ResearchFormalization.BatchR0608Claim26351
