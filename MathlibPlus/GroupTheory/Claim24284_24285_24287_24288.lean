import MathlibPlus.Open.ResearchFormalization.R0730Claim24286
import MathlibPlus.Open.ResearchFormalization.R0730Claim24289
import MathlibPlus.Open.ResearchFormalization.R0730Claim24294

namespace MathlibPlus.GroupTheory.R0730

open MathlibPlus.Open.ResearchFormalization.R0730Claim24294

/-- Claim 24284: the corrected canonical mixed-prism map on the concrete
`DihedralGroup (2*m)` carrier has the four parity branches and is bijective. -/
def dihedralMixedPrismParityMap_claim24284 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    Function.Bijective (mixedPrismMap m) ∧
    Nat.card (MixedPrismGroup m) = 4 * m ∧
    (∀ i : ZMod (2 * m), Even i.val →
      mixedPrismMap m (DihedralGroup.r i) = DihedralGroup.r i) ∧
    (∀ i : ZMod (2 * m), ¬ Even i.val →
      mixedPrismMap m (DihedralGroup.r i) =
        DihedralGroup.r (1 - i) * DihedralGroup.sr 0) ∧
    (∀ j : ZMod (2 * m), Even (-j).val →
      mixedPrismMap m (DihedralGroup.sr j) =
        DihedralGroup.r ((m : ZMod (2 * m)) - (-j))) ∧
    (∀ j : ZMod (2 * m), ¬ Even (-j).val →
      mixedPrismMap m (DihedralGroup.sr j) =
        DihedralGroup.r ((m : ZMod (2 * m)) + (-j) + 1) *
          DihedralGroup.sr 0) ∧
    (rotationGenerator m) ^ (2 * m) = 1 ∧
    (reflectionGenerator m) ^ 2 = 1 ∧
    reflectionGenerator m * rotationGenerator m * reflectionGenerator m =
      (rotationGenerator m)⁻¹

/-- Claim 24285: the connected prism base has the explicit right-Cayley
isomorphism with the corrected mixed-prism map, including inverse closure and
generation of both connection sets. -/
def connectedPrismBaseMapped_claim24285 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    let G := MixedPrismGroup m
    let r := rotationGenerator m
    let s := reflectionGenerator m
    let S : Set G := {r, r⁻¹, s}
    let T : Set G := {s, r ^ 2 * s, r ^ m}
    (∀ x ∈ S, x⁻¹ ∈ S) ∧
      (∀ x ∈ T, x⁻¹ ∈ T) ∧
      Subgroup.closure S = ⊤ ∧
      Subgroup.closure T = ⊤ ∧
      sameCayleyIsomorphism S T (mixedPrismMap m)

/-- Claim 24287: the canonical set-valued atom derivative is independent of
vertex exactly when it has one common target atom. -/
def setValuedAtomDerivativeAndStability_claim24287 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    ∀ A : Set (MixedPrismGroup m),
      independentlyStable m A ↔
        ∃ θ : Set (MixedPrismGroup m),
          ∀ g, atomDerivative m A g = θ ∧
            θ = targetAtom m A

/-- Claim 24288: every inverse rotation atom has the parity-classified target
under the corrected concrete mixed-prism map, with a singleton at the odd
half-turn. -/
def inverseRotationAtomsStable_claim24288 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    ∀ k : ℕ, 1 ≤ k → k ≤ m →
      independentlyStable m (inverseRotationAtom m k) ∧
      ((Even k ∧ targetAtom m (inverseRotationAtom m k) =
          inverseRotationAtom m k) ∨
       (Odd k ∧ targetAtom m (inverseRotationAtom m k) =
          {DihedralGroup.r ((1 : ZMod (2 * m)) + (k : ZMod (2 * m))) *
             DihedralGroup.sr 0,
           DihedralGroup.r ((1 : ZMod (2 * m)) - (k : ZMod (2 * m))) *
             DihedralGroup.sr 0})) ∧
      (k = m → targetAtom m (inverseRotationAtom m k) =
        {DihedralGroup.r ((1 : ZMod (2 * m)) + (k : ZMod (2 * m))) *
          DihedralGroup.sr 0})

end MathlibPlus.GroupTheory.R0730
