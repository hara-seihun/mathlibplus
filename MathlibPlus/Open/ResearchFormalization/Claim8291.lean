import Mathlib
import MathlibPlus.Open.AnalyticNumberTheory.Claim8285

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators

/-- Claim 8291: the finite-u Jordan expansion and its absolute exchange bound. -/
def finiteUJordanExpansionClaim8291 : Prop :=
  let M : ℕ → ℝ → ℝ := fun N t ↦
    ∑' b : ℕ,
      if Nat.Coprime (b + 1) N then
        (((ArithmeticFunction.moebius (b + 1) : ℤ) : ℝ) /
            ((b + 1 : ℕ) : ℝ)) *
          Real.exp (-t * ((b + 1 : ℕ) : ℝ))
      else 0
  let K : ℕ → ℝ → ℝ → ℝ := fun N x y ↦
    ∑' a : ℕ,
      if Nat.Coprime (a + 1) N then
        (Real.exp (-y * ((a + 1 : ℕ) : ℝ)) /
            ((a + 1 : ℕ) : ℝ)) *
          M N (((a + 1 : ℕ) : ℝ) * x)
      else 0
  let J : ℕ → ℕ → ℝ := fun k n ↦
    (n : ℝ) ^ k *
      ∏ p ∈ n.primeFactors, (1 - ((p : ℝ)⁻¹) ^ k)
  ∀ N : ℕ, Squarefree N → 2 ≤ N →
    ∀ u : ℝ, 0 < u →
      (K N (u * (N : ℝ)) u =
          Real.exp (-u * (N : ℝ)) +
            ∑' k : ℕ,
              if 1 ≤ k then
                ((-u) ^ k / (Nat.factorial k : ℝ)) *
                  (∑' n : ℕ,
                    if 1 ≤ n ∧ Nat.Coprime n N then
                      J k n / (n : ℝ) *
                        Real.exp (-u * (N : ℝ) * (n : ℝ))
                    else 0)
              else 0) ∧
        Summable (fun ab : ℕ × ℕ ↦
          if 1 ≤ ab.1 ∧ 1 ≤ ab.2 then
            |(((ArithmeticFunction.moebius ab.2 : ℤ) : ℝ))| /
                ((ab.1 : ℝ) * (ab.2 : ℝ)) *
              Real.exp
                (-u * (ab.1 : ℝ) *
                  ((N : ℝ) * (ab.2 : ℝ) - 1))
          else 0)

end

end MathlibPlus.Open.ResearchFormalization
