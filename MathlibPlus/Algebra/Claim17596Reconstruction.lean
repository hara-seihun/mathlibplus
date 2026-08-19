import MathlibPlus.Algebra.ExactTwoShearCommutator

namespace MathlibPlus.Algebra.Claim17596

noncomputable section

abbrev RealMatrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The wall-crossing commutator built from the two exact shears. -/
def shearCommutator17596 (a b : ℝ) : RealMatrix2 :=
  upperShear a * lowerShear b * (upperShear a)⁻¹ * (lowerShear b)⁻¹

/-- The explicit commutator matrix used by the wall crossing. -/
def explicitShearCommutator17596 (a b : ℝ) : RealMatrix2 :=
  !![1 + a * b + a ^ 2 * b ^ 2, -(a ^ 2 * b);
     a * b ^ 2, 1 - a * b]

/-- The symmetric Maslov matrix attached to the commutator parameters. -/
def maslovMatrix17596 (a b : ℝ) : RealMatrix2 :=
  !![2 * a * b ^ 2 / (a ^ 2 * b ^ 2 + 4),
     -a * b * (a * b + 2) / (a ^ 2 * b ^ 2 + 4);
     -a * b * (a * b + 2) / (a ^ 2 * b ^ 2 + 4),
     2 * a ^ 2 * b / (a ^ 2 * b ^ 2 + 4)]

/-- The exact wall data and transmission relation for a positive `ρ`. -/
def transmissionWallRelation17596 (a b τ ρ : ℝ) : Prop :=
  shearCommutator17596 a b = explicitShearCommutator17596 a b ∧
    -Matrix.det (maslovMatrix17596 a b) = τ ^ 2 ∧
    0 < ρ ∧ |τ| < 1 ∧
    (a * b) ^ 2 = ρ + ρ⁻¹ - 2 ∧
    ρ + ρ⁻¹ - 2 = 4 * τ ^ 2 / (1 - τ ^ 2)

/-- The wall-crossing chain determines `ρ` up to reciprocal exchange, and the
branch `ρ ≥ 1` removes that exchange. -/
def reconstructRhoFromWallCrossing_claim17596 : Prop :=
  ∀ (a b τ ρ₁ ρ₂ : ℝ),
    transmissionWallRelation17596 a b τ ρ₁ →
    transmissionWallRelation17596 a b τ ρ₂ →
    (ρ₂ = ρ₁ ∨ ρ₂ = ρ₁⁻¹) ∧
      (1 ≤ ρ₁ → 1 ≤ ρ₂ → ρ₂ = ρ₁)

end

end MathlibPlus.Algebra.Claim17596
