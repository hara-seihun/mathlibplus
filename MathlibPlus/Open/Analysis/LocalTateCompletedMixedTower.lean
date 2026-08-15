import Mathlib

namespace MathlibPlus.Open.Analysis

abbrev C2 := Fin 2 → ℂ

abbrev V (k : ℕ) := SymmetricPower ℂ (Fin k) C2

abbrev M (k : ℕ) := TensorProduct ℂ (V k) (V k)

abbrev MHat (k : ℕ) :=
  DirectSum (Fin (k / 2 + 1)) (fun r => M (k - 2 * (r : ℕ)))

def localTateCompletedMixedTower : Prop :=
  ∀ k : ℕ, Module.finrank ℂ (MHat k) = Nat.choose (k + 3) 3

end MathlibPlus.Open.Analysis
