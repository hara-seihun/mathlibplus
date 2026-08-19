import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0730Claim24286

abbrev MixedPrismGroup (m : ℕ) := DihedralGroup (2 * m)

def rotationGenerator (m : ℕ) : MixedPrismGroup m :=
  DihedralGroup.r 1

def inverseRotationAtom (m k : ℕ) : Set (MixedPrismGroup m) :=
  {(rotationGenerator m) ^ k, ((rotationGenerator m) ^ k)⁻¹}

def claim24286 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    inverseRotationAtom m m = {(rotationGenerator m) ^ m}

end MathlibPlus.Open.ResearchFormalization.R0730Claim24286
