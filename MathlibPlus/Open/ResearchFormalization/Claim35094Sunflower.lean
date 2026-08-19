import MathlibPlus.Open.Research.BatchR1989.Claim35096

namespace MathlibPlus.Open.ResearchFormalization.Claim35094

open MathlibPlus.Open.Research.BatchR1989Claim35096

noncomputable section

/-- The exact three-heavy-direction binary sunflower, including the displayed
pullback-space identities and the proper pair projections of the deficient
triple image. -/
def exactPairwiseSunflowerWithDeficientTripleImage_claim35094 : Prop :=
  ∀ (n : ℕ) (h : 5 ≤ n),
    (∀ i : Fin 3,
      pullbackU h i =
        Submodule.span F2
          {zCharacter h + coordinate (heavyIndex3 h i),
            heavyCoordinate3 h, heavyCoordinate4 h}) ∧
    (∀ i : Fin 3,
      pullbackA h i =
        Submodule.span F2
          {zCharacter h, coordinate (heavyIndex3 h i),
            heavyCoordinate3 h, heavyCoordinate4 h}) ∧
    (∀ i j : Fin 3, i ≠ j →
      pullbackA h i ⊓ pullbackA h j = pullbackCenter h) ∧
    (∀ i j : Fin 3, i ≠ j →
      pairImage h i j = diagonalImage) ∧
    (∀ i j k : Fin 3, distinctThree i j k →
      tripleImage h i j k = deficientTripleImage) ∧
    (∀ i j k : Fin 3, distinctThree i j k →
      ∃ P : Submodule F2 (W × W),
        (P : Set (W × W)) =
          pairProjection12 (tripleImage h i j k) ∧
        (P : Set (W × W)) ⊂ pairImage h i j)

end

end MathlibPlus.Open.ResearchFormalization.Claim35094
