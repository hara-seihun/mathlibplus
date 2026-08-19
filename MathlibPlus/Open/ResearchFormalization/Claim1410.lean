import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim1410

/-- For every real displayed endpoint, the even floor and the shifted lower
endpoint satisfy the exact strict/weak interval. -/
def exactEvenFloorInterval : Prop :=
  ∀ Dtilde : ℝ,
    let D : ℝ := 2 * (Int.floor (Dtilde / 2) : ℝ)
    let W : ℝ := Dtilde - 2
    W < D ∧ D ≤ Dtilde

end MathlibPlus.Open.ResearchFormalization.Claim1410
