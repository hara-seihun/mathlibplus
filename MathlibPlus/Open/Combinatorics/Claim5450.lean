import MathlibPlus.Open.Combinatorics.Claim5451

namespace MathlibPlus.Open.Combinatorics.Claim5450

noncomputable section

open MathlibPlus.Open.Combinatorics.Claim5451
open MathlibPlus.Open.Combinatorics.Claim5457

/-- Claim 5450: the four displayed path second-jet functions are taken on the
rooted-vertex carrier, and `W(P_k)` is their span after restriction to the
path-automorphism coinvariants. -/
def fourSecondJetPathMoments_claim5450 : Prop :=
  ∀ k : ℕ,
    (∀ i : Fin 4,
      pathFourMoments k i ∈ pathOrbitSpace k) ∧
      (∀ f : pathOrbitSpace k,
        f ∈ pathMomentSubspace k ↔
          (f : Fin k → ℚ) ∈
            Submodule.span ℚ
              {constantMoment k,
                degreeMoment k,
                secondDegreeMoment k,
                secondJetMoment k})

end

end MathlibPlus.Open.Combinatorics.Claim5450
