import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def repairedProfile : Polynomial ℝ :=
    1
      - Polynomial.C (272266.323948868412576203020151 : ℝ) * Polynomial.X
      + Polynomial.C (90577.400735634916403319064733 : ℝ) * Polynomial.X ^ 2
      - Polynomial.C (11341.5840677203083986344425339 : ℝ) * Polynomial.X ^ 3
      + Polynomial.C (633.354229208277477295679752751 : ℝ) * Polynomial.X ^ 4
      - Polynomial.C (13.3059076794381404815117878395 : ℝ) * Polynomial.X ^ 5

def repaired_degree_five_profile : Prop :=
  repairedProfile.natDegree = 5 ∧
    ∀ u : ℝ,
      repairedProfile.eval u =
        1
          - (272266.323948868412576203020151 : ℝ) * u
          + (90577.400735634916403319064733 : ℝ) * u ^ 2
          - (11341.5840677203083986344425339 : ℝ) * u ^ 3
          + (633.354229208277477295679752751 : ℝ) * u ^ 4
          - (13.3059076794381404815117878395 : ℝ) * u ^ 5

end MathlibPlus.Open.Analysis
