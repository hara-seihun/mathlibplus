import MathlibPlus.Open.Research.NonsplitSingerLiftObstruction

namespace MathlibPlus.Open.Research.R2712

open MathlibPlus.Open.Research.NonsplitSingerLiftObstruction
open MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

/-- Preservation restricted to the two even nonzero-vector colors (3 and 4)
    in the explicit upstairs displacement coloring. -/
def preservesEvenUpstairsColors {r : ℕ}
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r)
    (η : F3Vector r → ZMod 2)
    (s : C2Quotient r → ZMod 2) : Prop :=
  ∀ p q : C4Cover r,
    (upstairsColor η (q - p) = 3 ∨ upstairsColor η (q - p) = 4) →
      upstairsColor η
          (blockLift (quotientLinearEquiv B) s q -
            blockLift (quotientLinearEquiv B) s p) =
        upstairsColor η (q - p)

/-- A switch is constant on each of the two quotient parity layers. -/
def parityLayerConstant {r : ℕ}
    (s : C2Quotient r → ZMod 2) : Prop :=
  ∀ ε : ZMod 2, ∃ c : ZMod 2, ∀ v : F3Vector r, s (ε, v) = c

/-- The same switch is specified by one global C₂ value on each parity layer. -/
def twoGlobalLayerSwitches {r : ℕ}
    (s : C2Quotient r → ZMod 2) : Prop :=
  ∃ c₀ c₁ : ZMod 2,
    ∀ (ε : ZMod 2) (v : F3Vector r),
      s (ε, v) = if ε = 0 then c₀ else c₁

/-- Claim 42369: preserving the two even upstairs orbital colors forces the
    C₂ switch to be constant in the vector coordinate on each parity layer,
    equivalently leaving one global switch value on each layer. -/
def claim42369 : Prop :=
  ∀ (r : ℕ)
    (B : F3Vector r ≃ₗ[ZMod 3] F3Vector r)
    (η : F3Vector r → ZMod 2)
    (s : C2Quotient r → ZMod 2),
    preservesEvenUpstairsColors B η s →
      parityLayerConstant s ∧ twoGlobalLayerSwitches s

end MathlibPlus.Open.Research.R2712
