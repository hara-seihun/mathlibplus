import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.FiniteWeylOddLineCapacity

noncomputable section

/-- The weight-basis carrier of `M_k = Sym^k (ℂ²) ⊗ Sym^k (ℂ²)`. -/
abbrev CoefficientIndex (k : ℕ) := Fin (k + 1) × Fin (k + 1)
abbrev CoefficientSpace (k : ℕ) := CoefficientIndex k → ℂ

/-- Reversal of the weight basis for `Sym^k (ℂ²)`. -/
def reverseIndex (k : ℕ) (r : Fin (k + 1)) : Fin (k + 1) :=
  ⟨k - r.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/-- The factor-swap action `S` from the admitted coefficient representation. -/
def factorSwap (k : ℕ) : Matrix (CoefficientIndex k) (CoefficientIndex k) ℂ :=
  fun p q => if p = (q.2, q.1) then 1 else 0

/-- The left reversal action `J_k ⊗ I`, i.e. the action of `s₁`. -/
def leftReversal (k : ℕ) : Matrix (CoefficientIndex k) (CoefficientIndex k) ℂ :=
  fun p q => if p = (reverseIndex k q.1, q.2) then 1 else 0

/-- The ordered class indices used by the admitted `D₈` character table. -/
def classS₀ : Fin 8 := 4
def classS₁ : Fin 8 := 6

/-- The one-dimensional character with generator signs `(a,b)`. -/
def oneDimensionalCharacter (a b : ℂ) : Fin 8 → ℂ :=
  ![1, a * b, 1, a * b, a, a, b, b]

/-- The all-degree multiplicity formula supplied for the four one-dimensional
characters, with `n = k+1` and `j=1` in even degree and `j=0` in odd degree. -/
def oneDimensionalMultiplicity (k : ℕ) (a b : ℂ) : ℂ :=
  let n : ℂ := (k + 1 : ℕ)
  let j : ℂ := if Even k then 1 else 0
  (n ^ 2 + j ^ 2 + 2 * j * a * b + 2 * n * a + 2 * n * j * b) / 8

/-- Natural-number form of `floor ((k+1)/2)^2`; natural division is the
floor in the displayed capacity formula. -/
def s₁OddCapacity (k : ℕ) : ℕ :=
  ((k + 1) / 2) ^ 2

/-- The simultaneous `(s₀,s₁)=(a,b)` eigenspace in the concrete coefficient
module. -/
def characterEigenspace (k : ℕ) (a b : ℂ) :
    Submodule ℂ (CoefficientSpace k) :=
  (LinearMap.ker
      ((factorSwap k).mulVecLin -
        a • (LinearMap.id : CoefficientSpace k →ₗ[ℂ] CoefficientSpace k))) ⊓
    (LinearMap.ker
      ((leftReversal k).mulVecLin -
        b • (LinearMap.id : CoefficientSpace k →ₗ[ℂ] CoefficientSpace k)))

/-- The target isotypic carrier for the two `s₁`-odd one-dimensional
characters `χ_{+,-}` and `χ_{-,-}`. -/
def s₁OddTarget (k : ℕ) : Submodule ℂ (CoefficientSpace k) :=
  characterEigenspace k 1 (-1) ⊔ characterEigenspace k (-1) (-1)

abbrev FourSourceLines := Fin 4 → ℂ

/-- The source action of `s₀` on four independent lines with extensions
specified by their signs. -/
def sourceS₀ (a : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal a

/-- Every source line in this carrier is `s₁`-odd. -/
def sourceS₁ : Matrix (Fin 4) (Fin 4) ℂ :=
  (-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- Equivariance of a four-line source map for the concrete coefficient
representation, together with its target `s₁`-odd isotypic constraint. -/
def fourOddEquivariant (k : ℕ) (a : Fin 4 → ℂ)
    (B : FourSourceLines →ₗ[ℂ] CoefficientSpace k) : Prop :=
  (∀ i : Fin 4, a i = 1 ∨ a i = -1) ∧
    (∀ v : FourSourceLines,
      B ((sourceS₀ a).mulVec v) = (factorSwap k).mulVec (B v)) ∧
    (∀ v : FourSourceLines,
      B (sourceS₁.mulVec v) = (leftReversal k).mulVec (B v)) ∧
    LinearMap.range B ≤ s₁OddTarget k

/-- Rank of the target image of a concrete source map. -/
def targetImageRank {k : ℕ}
    (B : FourSourceLines →ₗ[ℂ] CoefficientSpace k) : ℕ :=
  Module.finrank ℂ (LinearMap.range B)

/-- The exact maximum-rank assertion for four independent `s₁`-odd source
lines. The domain `Fin 4 → ℂ` is their direct sum; all witnesses are required
to be equivariant for the displayed concrete actions. -/
def hasMaximumFourOddImageRank (k r : ℕ) : Prop :=
  (∀ (a : Fin 4 → ℂ) (B : FourSourceLines →ₗ[ℂ] CoefficientSpace k),
    fourOddEquivariant k a B → targetImageRank B ≤ r) ∧
    (∃ (a : Fin 4 → ℂ) (B : FourSourceLines →ₗ[ℂ] CoefficientSpace k),
      fourOddEquivariant k a B ∧ targetImageRank B = r)

/-- Claim 14730: an `s₁`-odd line has exactly the two indicated one-dimensional
extensions; their admitted multiplicity sum is the target capacity, and the
concrete equivariant image rank of four independent such lines is `1,1,4,4`
for degrees `1,2,3,4`, with rank four first possible at degree three. -/
def s1OddLineCapacityAndSharpThreshold_claim14730 : Prop :=
  (∀ (a b : ℂ),
      (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
        (oneDimensionalCharacter a b classS₁ = -1 ↔
          ((a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = -1)))) ∧
    (∀ k : ℕ,
      oneDimensionalMultiplicity k 1 (-1) +
          oneDimensionalMultiplicity k (-1) (-1) =
        (s₁OddCapacity k : ℂ)) ∧
    (∀ k : ℕ,
      Module.finrank ℂ (s₁OddTarget k) = s₁OddCapacity k) ∧
    (hasMaximumFourOddImageRank 1 1 ∧
      hasMaximumFourOddImageRank 2 1 ∧
      hasMaximumFourOddImageRank 3 4 ∧
      hasMaximumFourOddImageRank 4 4) ∧
    (∀ k : ℕ,
      hasMaximumFourOddImageRank k 4 ↔ 3 ≤ k)

end
end MathlibPlus.Open.ResearchFormalization.FiniteWeylOddLineCapacity
