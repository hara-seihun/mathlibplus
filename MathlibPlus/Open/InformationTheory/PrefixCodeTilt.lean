import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.InformationTheory

/-- A finite binary code with no codeword a proper prefix of another. -/
def BinaryPrefixFree (C : Finset (List Bool)) : Prop :=
  ∀ ⦃u v : List Bool⦄,
    u ∈ C → v ∈ C → u ≠ v →
      ¬ ∃ suffix : List Bool, v = u ++ suffix

/-- The Kraft sum of a finite binary code. -/
noncomputable def KraftSum (C : Finset (List Bool)) : ℝ :=
  Finset.sum C (fun word => ((2 : ℝ)⁻¹) ^ word.length)

/-- A finite complete binary prefix code, expressed by prefix-freeness and Kraft equality. -/
def CompleteBinaryPrefixCode (C : Finset (List Bool)) : Prop :=
  BinaryPrefixFree C ∧ KraftSum C = 1

/-- The tilted partition sum of a finite binary prefix code. -/
noncomputable def TiltedPartitionSum (q : ℝ) (C : Finset (List Bool)) : ℝ :=
  Finset.sum C (fun word => q ^ word.length)

/--
The complete-prefix hypotheses do not force distinct finite binary codes to
have different partition sums at every nonzero real length tilt in
`(1/2, 1)`.
-/
def claim_10540 : Prop :=
  ¬ ∀ C₁ C₂ : Finset (List Bool),
      CompleteBinaryPrefixCode C₁ →
      CompleteBinaryPrefixCode C₂ →
      C₁ ≠ C₂ →
      ∀ q : ℝ, (1 / 2 : ℝ) < q → q < 1 →
        TiltedPartitionSum q C₁ ≠ TiltedPartitionSum q C₂

end MathlibPlus.Open.InformationTheory
