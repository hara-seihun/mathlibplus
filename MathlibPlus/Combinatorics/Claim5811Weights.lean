import Mathlib

namespace MathlibPlus.Combinatorics.Claim5811

/-- The generalized-degree vertex weight with state `0` and the positive states
represented by `Fin (m + 1)` and `Fin m`, respectively. -/
def vertexWeight_claim5811
    (m : ℕ) (_hm : 1 ≤ m) {R : Type*} [One R]
    (x : Fin m → R) : Fin (m + 1) → R :=
  Fin.cases 1 x

/-- The generalized-degree interaction weight: state `0` has diagonal weight
one, the positive diagonal at `i` has weight `z i`, and every unequal pair has
common weight `y`. -/
def interactionWeight_claim5811
    (m : ℕ) (_hm : 1 ≤ m) {R : Type*} [One R]
    (z : Fin m → R) (y : R) :
    Fin (m + 1) → Fin (m + 1) → R :=
  fun s t =>
    if s = 0 ∧ t = 0 then 1
    else if s = t then Fin.cases 1 z s
    else y

end MathlibPlus.Combinatorics.Claim5811
