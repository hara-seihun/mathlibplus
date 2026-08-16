import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The fixed dyadic reflection doublet from the admitted statement. -/
def dyadicPlus (s : ℂ) : ℂ :=
  Complex.cpow (2 : ℂ) (-s)

def dyadicMinus (s : ℂ) : ℂ :=
  Complex.cpow (2 : ℂ) (-(1 - s))

/--
Componentwise multiplication by the fixed dyadic reflection doublet preserves
the two component swap identities.
-/
def reflectionCovariantDyadicProduct : Prop :=
  ∀ (ZPlus ZMinus : ℂ → ℂ),
    (∀ s : ℂ, ZPlus (1 - s) = ZMinus s) →
    (∀ s : ℂ, ZMinus (1 - s) = ZPlus s) →
      let YPlus : ℂ → ℂ := fun s => dyadicPlus s * ZPlus s
      let YMinus : ℂ → ℂ := fun s => dyadicMinus s * ZMinus s
      (∀ s : ℂ, YPlus (1 - s) = YMinus s) ∧
        (∀ s : ℂ, YMinus (1 - s) = YPlus s)

end MathlibPlus.Open.Analysis
