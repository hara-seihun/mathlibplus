import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1675CyclicGradient

noncomputable section

/-- Claim 33178: the cyclic difference image on the exact prime field is
precisely the zero-sum subspace; every zero-sum one-form has a unique
zero-normalized potential. -/
def everyZeroPeriodCyclicOneFormIsGradient_claim33178 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∀ f : ZMod p → ZMod p,
      (∑ s : ZMod p, f s = 0 ↔
        ∃! n : ZMod p → ZMod p,
          n 0 = 0 ∧
            ∀ s : ZMod p, f s = n (s + 1) - n s)) ∧
    Nat.card {f : ZMod p → ZMod p // ∑ s : ZMod p, f s = 0} =
      p ^ (p - 1)

end

end MathlibPlus.Open.ResearchFormalization.R1675CyclicGradient
