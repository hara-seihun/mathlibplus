import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim37236

private abbrev H := ZMod 7 × ZMod 3
private abbrev W := ZMod 7 × ZMod 7

private def hMul (h k : H) : H :=
  (h.1 + (2 : ZMod 7) ^ h.2.val * k.1, h.2 + k.2)

private def hScalar (h : H) (w : W) : W :=
  ((2 : ZMod 7) ^ h.2.val * w.1,
    (2 : ZMod 7) ^ h.2.val * w.2)

private def normalizedCocycle (z : H → W) : Prop :=
  z (0, 0) = 0 ∧
    ∀ h k : H, z (hMul h k) = z h + hScalar h (z k)

private def torusParameter (s : W) (i : ZMod 3) : W :=
  if i.val = 0 then 0 else if i.val = 1 then s else 3 • s

private def displayedCocycle (v s : W) : H → W :=
  fun h => (h.1 • v) + torusParameter s h.2

/-- Every normalized matching-scalar W-valued cocycle has the exact displayed
    four-parameter form, and every displayed parameter pair is a cocycle. -/
def claim37236 : Prop :=
  (∀ v s : W, normalizedCocycle (displayedCocycle v s)) ∧
    (∀ z : H → W, normalizedCocycle z →
      ∃ v s : W, ∀ (a : ZMod 7) (i : ZMod 3),
        z (a, i) = displayedCocycle v s (a, i)) ∧
    Nat.card {z : H → W // normalizedCocycle z} = 7 ^ 4

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim37236
