import Mathlib
import MathlibPlus.Open.NewResearch2.RationalHankel15108

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.Research.RationalRecovery

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankel15108
open MathlibPlus.Open.NewResearch2.RationalHankelStructure

 def exactCommonFactorEquivalences_claim3274 : Prop :=
  ∀ (d : ℕ) (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ),
    properVectorRationalModel P Q →
      let G := commonFroissartDivisor P Q
      let Qstar := reducedDenominator P Q
      ∀ S : Polynomial ℂ, S ∣ Q →
        (S ∣ G ↔ ∀ i : Fin d, S ∣ P i) ∧
          (S ∣ G ↔
            ∀ (i : Fin d) (z : ℂ) (k : ℕ),
              k < Polynomial.rootMultiplicity z S →
                normalizedHermiteJet (P i) z k = 0) ∧
          (S ∣ G ↔ minimalRecurrenceCancellation S Q Qstar) ∧
          (S ∣ G ↔ divisionLeavesRationalFunctionUnchanged P Q S)

end
end MathlibPlus.Open.Research.RationalRecovery
