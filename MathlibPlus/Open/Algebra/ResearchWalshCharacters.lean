import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.ResearchWalshCharacters

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Edge coordinates are the two-element vertex subsets of the labelled
complete graph on `Fin n`. -/
abbrev EdgeCoordinate (n : ℕ) := {e : Finset (Fin n) // e.card = 2}
abbrev GraphBooleanCube (n : ℕ) := EdgeCoordinate n → Bool

def walshCharacter {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (x : ι → Bool) : ℚ :=
  (-1 : ℚ) ^ (A.filter (fun i => x i = true)).card

def symmetricDifference {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) : Finset ι := (A \ B) ∪ (B \ A)

/-- Claim 5040: the Walsh characters indexed by all edge subsets are an
orthogonal basis of rational functions on the labelled graph Boolean cube. -/
def walshCharactersOrthogonalBasis_claim5040 : Prop :=
  ∀ n : ℕ,
    (∀ A B : Finset (EdgeCoordinate n), A ≠ B →
      ∑ x : GraphBooleanCube n,
        walshCharacter A x * walshCharacter B x = 0) ∧
    LinearIndependent ℚ (fun A : Finset (EdgeCoordinate n) =>
      walshCharacter A) ∧
    (∀ f : GraphBooleanCube n → ℚ,
      ∃ c : Finset (EdgeCoordinate n) → ℚ,
        f = ∑ A : Finset (EdgeCoordinate n), c A • walshCharacter A)

end
end MathlibPlus.Open.Algebra.ResearchWalshCharacters
