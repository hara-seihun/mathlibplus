import MathlibPlus.Open.ResearchFormalization.R0765Claim26919

namespace MathlibPlus.Open.ResearchFormalization.R0765Claim26920

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0765Claim26919

noncomputable section

abbrev Coeff26920 :=
  MathlibPlus.Open.ResearchFormalization.R0765Claim26919.Coeff
abbrev RootedFactor26920 :=
  MathlibPlus.Open.ResearchFormalization.R0765Claim26919.RootedFactor
abbrev RootedTree26920 :=
  MathlibPlus.Open.ResearchFormalization.R0765Claim26919.RootedTree
abbrev CoeffFraction26920 := FractionRing Coeff26920

/-- The first outer-variable coefficient of a product of rooted factors is
its common closure times the multiplicity-preserving sum of cavity/closure
ratios. -/
def claim26920 : Prop :=
  ∀ (m : ℕ) (c : Fin 3 → ℚ)
    (q : Fin 3 → Multiset RootedTree26920),
    MathlibPlus.Open.ResearchFormalization.R0765Claim26919.matchedOrderPureCore
      m c q →
      ∀ i : Fin 3,
        algebraMap Coeff26920 CoeffFraction26920
            ((MathlibPlus.Open.ResearchFormalization.R0765Claim26919.factorProduct
              (q i)).coeff 1) =
          algebraMap Coeff26920 CoeffFraction26920
              (MathlibPlus.Open.ResearchFormalization.R0765Claim26919.closureProduct
                (q 0)) *
            ((q i).map (fun T =>
              algebraMap Coeff26920 CoeffFraction26920
                  (MathlibPlus.Open.ResearchFormalization.R0765Claim26919.cavity T) /
                algebraMap Coeff26920 CoeffFraction26920
                  (MathlibPlus.Open.ResearchFormalization.R0765Claim26919.closure T))).sum

end
end MathlibPlus.Open.ResearchFormalization.R0765Claim26920
