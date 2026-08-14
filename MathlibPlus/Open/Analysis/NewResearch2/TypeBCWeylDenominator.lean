import Mathlib

namespace MathlibPlus.Open.NewResearch2.TypeBC

noncomputable section
open scoped BigOperators Classical

def typeBCWeylDenominator (d : ℕ) (y : Fin d → ℝ) : ℝ :=
  (∏ j : Fin d, Real.sqrt (y j)) *
    ∏ j : Fin d, ((Finset.univ : Finset (Fin d)).filter (fun k => j < k)).prod
      (fun k => |(y j)^2 - (y k)^2|)

def claim17153 (d : ℕ) (y : Fin d → ℝ) : Prop :=
  (∀ j, 0 < y j) →
    typeBCWeylDenominator d y =
      (∏ j : Fin d, Real.rpow (y j) (1 / 2 : ℝ)) *
        ∏ j : Fin d, ((Finset.univ : Finset (Fin d)).filter (fun k => j < k)).prod
          (fun k => |(y j)^2 - (y k)^2|)

end
end MathlibPlus.Open.NewResearch2.TypeBC
