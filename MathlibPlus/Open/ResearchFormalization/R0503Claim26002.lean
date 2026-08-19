import MathlibPlus.Open.ResearchFormalization.R0503Claim26003

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0503Claim26002

noncomputable section

open MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001
open MathlibPlus.Open.ResearchFormalization.R0503Claim26003

abbrev Index := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Index
abbrev Composition := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Composition

/-- The incidence coefficient of a support in the pair residual
    `S₂-4S₁-S₆`. -/
def pairIncidenceCoefficient26002 (J : Finset (Fin 7)) : ℚ :=
  incidenceCount 2 J - 4 * incidenceCount 1 J - incidenceCount 6 J

def pairResidual26002 (N d : ℕ) (μ : Composition 7 N) : ℚ :=
  blockSum 2 (powerFunction N d) μ -
    4 * blockSum 1 (powerFunction N d) μ -
      blockSum 6 (powerFunction N d) μ

/-- Claim 26002: the exact pair-monomial incidence coefficient is `-4` on
    every support occurring in degrees one through three, the associated
    fixed-total residual is `-4N^d`, and the constant pair residual is
    constant across compositions. -/
def pairResidualIncidence_claim26002 : Prop :=
  (∀ (N d : ℕ), 1 ≤ d → d ≤ 3 →
    (∀ r : ℕ, 1 ≤ r → r ≤ d →
      ∀ J : Finset (Fin 7), J.card = r →
        pairIncidenceCoefficient26002 J = -4) ∧
      (∀ μ : Composition 7 N,
        pairResidual26002 N d μ = -4 * (N : ℚ) ^ d)) ∧
  (∀ N : ℕ, ∃ c : ℚ, ∀ μ : Composition 7 N,
    pairResidual26002 N 0 μ = c)

end

end MathlibPlus.Open.ResearchFormalization.R0503Claim26002
