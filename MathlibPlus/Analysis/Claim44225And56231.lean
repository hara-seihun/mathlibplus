-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Analysis.Claim44225

/-- A two-bit parity target has unit posterior variance before either query
and after the first fresh query, so every no-repeat complete policy has area 2. -/
theorem twoBitParityFreshPolicyArea_claim44225 :
    let Ω := Fin 2 → Bool
    let sgn : Bool → ℚ := fun b => if b then 1 else -1
    let parity : Ω → ℚ := fun x => sgn (x 0) * sgn (x 1)
    let fiber : List (Fin 2) → Ω → Finset Ω := fun q x =>
      Finset.univ.filter (fun y => ∀ i ∈ q, y i = x i)
    let mean : List (Fin 2) → Ω → ℚ := fun q x =>
      (∑ y ∈ fiber q x, parity y) / (fiber q x).card
    let varianceAfter : List (Fin 2) → ℚ := fun q =>
      (∑ x ∈ (Finset.univ : Finset Ω),
          (∑ y ∈ fiber q x, (parity y - mean q x) ^ 2) /
            (fiber q x).card) /
        Fintype.card Ω
    ∀ i : Fin 2,
      varianceAfter [] = 1 ∧
        varianceAfter [i] = 1 ∧
        (∀ j : Fin 2, i ≠ j → varianceAfter [i, j] = 0) ∧
        varianceAfter [] + varianceAfter [i] = 2 := by
  native_decide

end MathlibPlus.Analysis.Claim44225

namespace MathlibPlus.Analysis.Claim56231

/-- The three-coordinate finite Rademacher calculation behind claim 56231.
The area is the expected conditional variance after each listed query, with
uniform measure on `Fin 3 → Bool`. -/
theorem precedingBlocksContributeRealArea_claim56231 :
    let Ω := Fin 3 → Bool
    let sgn : Bool → ℚ := fun b => if b then 1 else -1
    let m : Ω → ℚ := fun x => (sgn (x 0) + sgn (x 1)) / 2
    let fiber : List (Fin 3) → Ω → Finset Ω := fun q x =>
      Finset.univ.filter (fun y => ∀ i ∈ q, y i = x i)
    let mean : List (Fin 3) → Ω → ℚ := fun q x =>
      (∑ y ∈ fiber q x, m y) / (fiber q x).card
    let varianceAfter : List (Fin 3) → ℚ := fun q =>
      (∑ x ∈ (Finset.univ : Finset Ω),
          (∑ y ∈ fiber q x, (m y - mean q x) ^ 2) / (fiber q x).card) /
        Fintype.card Ω
    let isolated : ℚ := varianceAfter [] + varianceAfter [0]
    let preceded : ℚ := varianceAfter [] + varianceAfter [2] + varianceAfter [2, 0]
    varianceAfter [] = 1 / 2 ∧
      varianceAfter [2] = 1 / 2 ∧
      varianceAfter [0] = 1 / 4 ∧
      varianceAfter [2, 0] = 1 / 4 ∧
      isolated = 3 / 4 ∧ preceded = 5 / 4 ∧ preceded - isolated = 1 / 2 := by
  native_decide

end MathlibPlus.Analysis.Claim56231
