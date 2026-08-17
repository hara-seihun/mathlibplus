import MathlibPlus.Open.ResearchFormalization.R1003Claim28182

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28175

open MathlibPlus.Open.ResearchFormalization.R1003.Claim28182

/-- The named semidirect-product presentation and its displayed coordinate law. -/
def semidirectProductE35 : Prop :=
  semidirectGroupIdentifications ∧
    ∀ (x y : ZMod 7) (r s : ZMod 5) (i j : ZMod 8),
      gMul (x, (r, i)) (y, (s, j)) =
        (x + (-1 : ZMod 7) ^ i.val * y,
          (r + (-1 : ZMod 5) ^ i.val * s, i + j))

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28175
