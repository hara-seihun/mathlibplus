import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Somlai

open Classical

abbrev SomlaiField (p : ℕ) := ZMod p
abbrev SomlaiU (p m : ℕ) := Fin m → SomlaiField p
abbrev SomlaiV (p m : ℕ) := Fin (m + 1) → SomlaiField p

def somlaiDelta {p m : ℕ} (v : SomlaiU p m)
    (f : SomlaiU p m → SomlaiField p) (x : SomlaiU p m) : SomlaiField p :=
  f (x + v) - f x

def somlaiCoordinateVector {p m : ℕ} (i : Fin m) : SomlaiU p m :=
  Pi.single i 1

def somlaiAllOnes {p m : ℕ} : SomlaiU p m :=
  fun _ => 1

def somlaiRepeatedComplement {p m : ℕ} (i : Fin m) : SomlaiU p m :=
  ∑ k ∈ (Finset.univ.filter (fun k : Fin m => k ≠ i)),
    somlaiCoordinateVector k

def somlaiTotalCoordinate {p m : ℕ}
    (r : SomlaiU p m → SomlaiV p m) (x : SomlaiU p m) : SomlaiField p :=
  ∑ j : Fin (m + 1), r x j

/-- Claim 42398: the exact lower-coordinate Somlai shear system. -/
def claim42398 (p m : ℕ) : Prop :=
  p.Prime ∧ 0 < m ∧
    ∃ r : SomlaiU p m → SomlaiV p m,
      r 0 = 0 ∧
      (∀ (i : Fin m) (x : SomlaiU p m),
        somlaiDelta (somlaiCoordinateVector i)
          (fun y => r y 0 + r y (Fin.succ i)) x = 0) ∧
      (∀ (i : Fin m) (x : SomlaiU p m),
        somlaiDelta (somlaiRepeatedComplement i)
          (fun y => somlaiTotalCoordinate r y + r y (Fin.succ i)) x = 0) ∧
      (∀ (x : SomlaiU p m),
        somlaiDelta somlaiAllOnes
          (fun y => somlaiTotalCoordinate r y) x = 1)

end MathlibPlus.Open.Somlai
