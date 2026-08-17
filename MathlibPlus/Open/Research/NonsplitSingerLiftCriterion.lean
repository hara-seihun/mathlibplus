import MathlibPlus.Open.Research.NonsplitSingerLiftObstruction

namespace MathlibPlus.Open.Research.NonsplitSingerLiftCriterion

open MathlibPlus.Open.Research.NonsplitSingerLiftObstruction

/-- The odd upstairs color is the layer bit plus the logarithm-parity bit. -/
def kappa {r : ℕ} (η : F3Vector r → ZMod 2)
    (a : ZMod 4) (v : F3Vector r) : ZMod 2 :=
  oddCoordinateBit a + η v

/-- Claim 42370: for a logarithm-parity character, an invertible quotient-linear
map has an orbital-preserving block lift exactly when its character difference
is constant on the nonzero vectors. -/
def claim42370 : Prop :=
  ∀ (r : ℕ)
    (S : F3Vector r ≃ₗ[ZMod 3] F3Vector r)
    (η : F3Vector r → ZMod 2),
    primitiveSingerLogParity S η →
    ∀ B : F3Vector r ≃ₗ[ZMod 3] F3Vector r,
      (∃ s : C2Quotient r → ZMod 2,
        preservesUpstairsTuple B η s) ↔
      (∃ c : ZMod 2, ∀ v : F3Vector r, v ≠ 0 →
        η (B v) + η v = c)

end MathlibPlus.Open.Research.NonsplitSingerLiftCriterion
