import MathlibPlus.Open.ResearchFormalization.R1330Claim41027

namespace MathlibPlus.Open.GroupTheory

open MathlibPlus.Open.Research.R1330Formalization_41037
open MathlibPlus.Open.ResearchFormalization.R1330Claim41027

noncomputable section

/-- Claim 41030: for every odd prime model, the exact mixed shear has the
source fixed-point equations and precisely the four points in {0,1}². -/
def mixedShearFixedPoints_claim41030 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∀ z : V p,
      mixedShear p z = z ↔
        binomTwo p z.1 = 0 ∧
          binomTwo p (z.2 - binomTwo p z.1) = 0) ∧
      (∀ z : V p,
        mixedShear p z = z ↔
          (z.1 = 0 ∨ z.1 = 1) ∧ (z.2 = 0 ∨ z.2 = 1)) ∧
      Nat.card {z : V p // mixedShear p z = z} = 4

end

end MathlibPlus.Open.GroupTheory
