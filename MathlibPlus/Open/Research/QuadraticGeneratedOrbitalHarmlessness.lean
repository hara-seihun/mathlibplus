import Mathlib
import MathlibPlus.Open.Research.QuadraticBatch

namespace MathlibPlus.Open.Research.QuadraticGeneratedOrbitalHarmlessness

abbrev PairPoint := MathlibPlus.Open.Research.QuadraticBatch.Omega
abbrev PairPermutation := Equiv.Perm PairPoint
abbrev PairRelation := PairPoint → PairPoint → Prop

/-- The ordered orbital of a pair for the displayed generated permutation group. -/
def generatedOrbital (G : Subgroup PairPermutation)
    (a b : PairPoint) : Set (PairPoint × PairPoint) :=
  {p | ∃ g : G,
    p = ((g : PairPermutation) a, (g : PairPermutation) b)}

/-- A relation obtained by fusing specified non-diagonal generated orbitals. -/
def directedGeneratedOrbitalFusion
    (G : Subgroup PairPermutation)
    (𝓕 : Set (Set (PairPoint × PairPoint)))
    (R : PairRelation) : Prop :=
  (∀ O, O ∈ 𝓕 → ∃ a b : PairPoint, a ≠ b ∧
    O = generatedOrbital G a b) ∧
  (∀ a b : PairPoint,
    R a b ↔ ∃ O, O ∈ 𝓕 ∧ (a, b) ∈ O)

/-- The extra symmetry and looplessness required of an undirected fusion. -/
def undirectedGeneratedOrbitalFusion
    (G : Subgroup PairPermutation)
    (𝓕 : Set (Set (PairPoint × PairPoint)))
    (R : PairRelation) : Prop :=
  directedGeneratedOrbitalFusion G 𝓕 R ∧
    (∀ a b, R a b ↔ R b a) ∧
    (∀ a, ¬ R a a)

/-- Preservation of one directed relation by a permutation. -/
def relationAutomorphism (R : PairRelation) (q : PairPermutation) : Prop :=
  ∀ a b : PairPoint, R a b ↔ R (q a) (q b)

/-- The exact displayed-pair certificate used for CI/DCI harmlessness. -/
def displayedPairHarmless
    (H : MathlibPlus.Open.Research.QuadraticBatch.Plane →
      MathlibPlus.Open.Research.QuadraticBatch.F3)
    (m : MathlibPlus.Open.Research.QuadraticBatch.Fiber →
      MathlibPlus.Open.Research.QuadraticBatch.F3)
    (R : PairRelation) : Prop :=
  relationAutomorphism R
      (MathlibPlus.Open.Research.QuadraticBatch.twist H m) ∧
    MathlibPlus.Open.Research.QuadraticBatch.InExactTwoClosure
      (MathlibPlus.Open.Research.QuadraticBatch.generatedPair H m)
      (MathlibPlus.Open.Research.QuadraticBatch.twist H m) ∧
    (∀ g : PairPermutation,
      g ∈ MathlibPlus.Open.Research.QuadraticBatch.translationGroup →
        MathlibPlus.Open.Research.QuadraticBatch.conjugateElement
            (MathlibPlus.Open.Research.QuadraticBatch.twist H m) g ∈
          MathlibPlus.Open.Research.QuadraticBatch.generatedPair H m) ∧
    (∀ g : PairPermutation,
      g ∈ MathlibPlus.Open.Research.QuadraticBatch.translationGroup →
        MathlibPlus.Open.Research.QuadraticBatch.InExactTwoClosure
          (MathlibPlus.Open.Research.QuadraticBatch.generatedPair H m)
          (MathlibPlus.Open.Research.QuadraticBatch.conjugateElement
            (MathlibPlus.Open.Research.QuadraticBatch.twist H m) g))

/-- Claim 41643: every directed or undirected generated-orbital fusion of the
 displayed pure one-direction pair is harmless through that pair. -/
def claim_41643 : Prop :=
  ∀ (H : MathlibPlus.Open.Research.QuadraticBatch.Plane →
      MathlibPlus.Open.Research.QuadraticBatch.F3)
    (m : MathlibPlus.Open.Research.QuadraticBatch.Fiber →
      MathlibPlus.Open.Research.QuadraticBatch.F3),
    MathlibPlus.Open.Research.QuadraticBatch.IsHomogeneousQuadratic m →
      ∀ (𝓕 : Set (Set (PairPoint × PairPoint))) (R : PairRelation),
        directedGeneratedOrbitalFusion
            (MathlibPlus.Open.Research.QuadraticBatch.generatedPair H m)
            𝓕 R →
          displayedPairHarmless H m R ∧
            (undirectedGeneratedOrbitalFusion
                (MathlibPlus.Open.Research.QuadraticBatch.generatedPair H m)
                𝓕 R → displayedPairHarmless H m R)

end MathlibPlus.Open.Research.QuadraticGeneratedOrbitalHarmlessness
