-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.GroupTheory

abbrev Claim29233BasePoint := ZMod 5 × ZMod 8

def claim29233WValue : Fin 4 → ZMod 8 := ![1, 3, 5, 7]

def claim29233Theta (u : (ZMod 5)ˣ) (v : ZMod 5) (w : Fin 4)
    (p : Claim29233BasePoint) : Claim29233BasePoint :=
  (↑u * p.1 + v * if p.2.val % 2 = 1 then 1 else 0,
    claim29233WValue w * p.2)

/-- The displayed `(u,v,w)` maps are permutations of the marked base-point
set; the marked-pair structure itself is source-specific. -/
theorem markedBaseTheta_bijective_claim29233 :
    ∀ (u : (ZMod 5)ˣ) (v : ZMod 5) (w : Fin 4),
      Function.Bijective (claim29233Theta u v w) := by
  native_decide

/-- The parameters have cardinality `4 · 5 · 4 = 80`. -/
theorem markedBaseTheta_count_claim29233 :
    Fintype.card ((ZMod 5)ˣ × ZMod 5 × Fin 4) = 80 := by
  native_decide

end MathlibPlus.GroupTheory
