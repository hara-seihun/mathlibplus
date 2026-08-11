import Mathlib

namespace MathlibPlus.Algebra.FiniteFieldBinomial

/-- Claim 30562: the quadratic binomial cross-effect is multiplication. -/
theorem binomialTwo_add_sub {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (x a : K) :
    (x + a) * (x + a - 1) / 2 - x * (x - 1) / 2 - a * (a - 1) / 2 = a * x := by
  field_simp [h2]
  ring

/-- The source's finite-field formulation, with `F_p` represented by `ZMod p`
and `c(t)` written as the displayed quadratic binomial polynomial. -/
theorem finiteFieldBinomialIdentity (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (x a : ZMod p) :
    let c : ZMod p → ZMod p := fun t => t * (t - 1) / 2
    c (x + a) - c x - c a = a * x := by
  dsimp
  apply binomialTwo_add_sub
  change ((2 : ℕ) : ZMod p) ≠ 0
  intro hzero
  have hdiv : p ∣ 2 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  have hp_le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have heq : p = 2 := by omega
  exact hpodd heq

end MathlibPlus.Algebra.FiniteFieldBinomial
