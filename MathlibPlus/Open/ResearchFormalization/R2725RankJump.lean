import MathlibPlus.Open.ResearchFormalizationBatch.R2725

namespace MathlibPlus.Open.ResearchFormalizationBatch.R2725RankJump

noncomputable section

open Classical

abbrev EquationRow (m n : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m ×
    (MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n → ZMod 3)

def linearFunctional42423 {n : ℕ}
    (φ : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n → ZMod 3) : Prop :=
  (∀ x y, φ (x + y) = φ x + φ y) ∧
    (∀ c x, φ (c • x) = c * φ x)

def validEquationRow42423 {m n : ℕ}
    (f : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m →
      MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n)
    (row : EquationRow m n) : Prop :=
  row.1 ≠ 0 ∧
    linearFunctional42423 row.2 ∧
      ∀ v ∈ MathlibPlus.Open.ResearchFormalizationBatch.derivativeSubspace f row.1,
        row.2 v = 0

def matrixShadowValue {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 3))
    (a : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m) :
    MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n :=
  fun j => ∑ i : Fin m, a i * M i j

def derivativeCoefficientMatrix {m n : ℕ}
    (f : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m →
      MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n) :
    Matrix (EquationRow m n) (Fin m × Fin n) (ZMod 3) :=
  fun row col =>
    if validEquationRow42423 f row then
      row.1 col.1 * row.2 (Pi.single col.2 1)
    else 0

def derivativeAugmentedMatrix {m n : ℕ}
    (f : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m →
      MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n) :
    Matrix (EquationRow m n) ((Fin m × Fin n) ⊕ Unit) (ZMod 3) :=
  fun row col =>
    match col with
    | Sum.inl ij => derivativeCoefficientMatrix f row ij
    | Sum.inr _ =>
        if validEquationRow42423 f row then row.2 (f row.1) else 0

def matrixNormalizedDerivativeEquations {m n : ℕ}
    (f : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m →
      MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n)
    (M : Matrix (Fin m) (Fin n) (ZMod 3)) : Prop :=
  ∀ row : EquationRow m n,
    ∑ col : Fin m × Fin n,
      derivativeCoefficientMatrix f row col * M col.1 col.2 =
        if validEquationRow42423 f row then row.2 (f row.1) else 0

/-- Claim 42423: a strict rank jump after adjoining the exact inhomogeneous
column of the normalized derivative system excludes every linear shadow. -/
def rankJumpObstruction_claim42423 : Prop :=
  ∀ (m n : ℕ)
    (f : MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector m →
      MathlibPlus.Open.ResearchFormalizationBatch.TernaryVector n),
    MathlibPlus.Open.ResearchFormalizationBatch.oddTernaryPolynomialMap f →
      Matrix.rank (derivativeAugmentedMatrix f) >
          Matrix.rank (derivativeCoefficientMatrix f) →
        ¬ ∃ M : Matrix (Fin m) (Fin n) (ZMod 3),
          matrixNormalizedDerivativeEquations f M

end
end MathlibPlus.Open.ResearchFormalizationBatch.R2725RankJump
