import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0730Claim24294

abbrev MixedPrismGroup (m : ℕ) := DihedralGroup (2 * m)

def rotationGenerator (m : ℕ) : MixedPrismGroup m :=
  DihedralGroup.r 1

def reflectionGenerator (m : ℕ) : MixedPrismGroup m :=
  DihedralGroup.sr 0

def inverseRotationAtom (m k : ℕ) : Set (MixedPrismGroup m) :=
  {(rotationGenerator m) ^ k, ((rotationGenerator m) ^ k)⁻¹}

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

def stableAtomFamily (m : ℕ) : Set (Set (MixedPrismGroup m)) :=
  {A |
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
      A = inverseRotationAtom m k ∧ independentlyStable m A) ∨
    (A = {reflectionGenerator m} ∧ independentlyStable m A) ∨
    (A = {(rotationGenerator m) ^ m * reflectionGenerator m} ∧
      independentlyStable m A)}

def baseAtomFamily (m : ℕ) : Set (Set (MixedPrismGroup m)) :=
  {inverseRotationAtom m 1, {reflectionGenerator m}}

def sourceConnectionSet (m : ℕ) (Ω : Set (Set (MixedPrismGroup m))) :
    Set (MixedPrismGroup m) :=
  inverseRotationAtom m 1 ∪ {reflectionGenerator m} ∪ ⋃₀ Ω

def targetConnectionSet (m : ℕ) (Ω : Set (Set (MixedPrismGroup m))) :
    Set (MixedPrismGroup m) :=
  targetAtom m (inverseRotationAtom m 1) ∪ targetAtom m {reflectionGenerator m} ∪
    ⋃₀ (targetAtom m '' Ω)

def cayleyAdjacency (S : Set (MixedPrismGroup m))
    (x y : MixedPrismGroup m) : Prop :=
  y * x⁻¹ ∈ S

def sameCayleyIsomorphism (S T : Set (MixedPrismGroup m))
    (e : MixedPrismGroup m → MixedPrismGroup m) : Prop :=
  Function.Bijective e ∧
    ∀ x y, cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

def claim24294 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    ∀ Ω : Set (Set (MixedPrismGroup m)),
      Ω ⊆ stableAtomFamily m \ baseAtomFamily m →
      sameCayleyIsomorphism (sourceConnectionSet m Ω)
        (targetConnectionSet m Ω) (mixedPrismMap m)

end MathlibPlus.Open.ResearchFormalization.R0730Claim24294
