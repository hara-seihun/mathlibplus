import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0730Claim24289

abbrev MixedPrismGroup (m : ℕ) := DihedralGroup (2 * m)

def rotationGenerator (m : ℕ) : MixedPrismGroup m :=
  DihedralGroup.r 1

def reflectionGenerator (m : ℕ) : MixedPrismGroup m :=
  DihedralGroup.sr 0

def mixedPrismMap (m : ℕ) : MixedPrismGroup m → MixedPrismGroup m
  | DihedralGroup.r i =>
      if Even i.val then
        DihedralGroup.r i
      else
        DihedralGroup.r (1 - i) * DihedralGroup.sr 0
  | DihedralGroup.sr j =>
      let i : ZMod (2 * m) := -j
      if Even i.val then
        DihedralGroup.r (m - i)
      else
        DihedralGroup.r ((m : ZMod (2 * m)) + i + 1) * DihedralGroup.sr 0

def atomDerivative (m : ℕ) (A : Set (MixedPrismGroup m))
    (g : MixedPrismGroup m) : Set (MixedPrismGroup m) :=
  {x | ∃ a, a ∈ A ∧
    x = mixedPrismMap m (a * g) * (mixedPrismMap m g)⁻¹}

def independentlyStable (m : ℕ) (A : Set (MixedPrismGroup m)) : Prop :=
  ∀ g, atomDerivative m A g = atomDerivative m A 1

def targetAtom (m : ℕ) (A : Set (MixedPrismGroup m)) : Set (MixedPrismGroup m) :=
  atomDerivative m A 1

def claim24289 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    let r := rotationGenerator m
    let s := reflectionGenerator m
    let A₀ : Set (MixedPrismGroup m) := {s}
    let Aₘ : Set (MixedPrismGroup m) := {r ^ m * s}
    independentlyStable m A₀ ∧
      independentlyStable m Aₘ ∧
      targetAtom m A₀ = {r ^ m} ∧
      targetAtom m Aₘ = {r * s}

end MathlibPlus.Open.ResearchFormalization.R0730Claim24289
