import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 33136: over `𝔽_p` for an odd prime `p`, the quadratic
`q(s) = s(s-1)/2` satisfies `q(s+1)-q(s)=s`.  The quotient by `2` is written
as multiplication by `2⁻¹`; this is definitionally available for every
`ZMod p`, and under the stated prime hypotheses it is the field quotient. -/
theorem binomialFiniteDifference_claim33136 (p : ℕ) (hp : Nat.Prime p)
    (hp2 : p ≠ 2) (s : ZMod p) :
    let q : ZMod p → ZMod p := fun t =>
      t * (t - 1) * (2 : ZMod p)⁻¹
    q (s + 1) - q s = s := by
  letI := Fact.mk hp
  dsimp
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    apply hp2
    exact le_antisymm (Nat.le_of_dvd (by norm_num) hdiv) hp.two_le
  field_simp [htwo]
  ring

end MathlibPlus.Algebra
