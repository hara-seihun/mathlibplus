import MathlibPlus.Open.Research.BaezDuarte

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim3451

noncomputable section

open MathlibPlus.Open.Research.BaezDuarte

/-- Claim 3451: the absolute reciprocal-zeta expansion of the named
Baez--Duarte coefficient sequence. -/
def mobiusExpansionOfBaezDuarteCoefficient3451 : Prop :=
  ∀ k : ℕ,
    (baezDuarteCoefficient k =
      ∑' n : ℕ+, reciprocalZetaTerm k n) ∧
      Summable (fun n : ℕ+ => ‖reciprocalZetaTerm k n‖)

end

end MathlibPlus.Open.ResearchFormalization.Claim3451
