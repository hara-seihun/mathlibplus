import MathlibPlus.Open.NumberTheory.Claim14746
import MathlibPlus.Open.Research.FormalizationBatch_01a00bf2_OrthogonalReflectionCompression

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim14751_14752

noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch_01a00bf2

/-- The exponent of the `r`th weight in `Sym^k(ℂ²)`. -/
def weightExponent (k : ℕ) (r : Fin (k + 1)) : ℤ :=
  (k : ℤ) - 2 * (r.1 : ℤ)

/-- The diagonal weight operator `D_k(z)` in the admitted weight basis. -/
def diagonalWeight (k : ℕ) (b : WeightBasis k) (z : ℂ) : V k →ₗ[ℂ] V k :=
  b.constr ℂ (fun r => (z ^ weightExponent k r) • b r)

/-- The mixed coefficient operator `T_k(y, α) = D_k(y) ⊗ D_k(α)`. -/
def mixedOperator (k : ℕ) (b : WeightBasis k) (y α : ℂ) : M k →ₗ[ℂ] M k :=
  TensorProduct.map (diagonalWeight k b y) (diagonalWeight k b α)

/-- The trace of the mixed operator in the induced tensor-product weight basis. -/
def mixedTrace (k : ℕ) (b : WeightBasis k) (y α : ℂ) : ℂ :=
  Matrix.trace
    (LinearMap.toMatrix (MixedBasis k b) (MixedBasis k b)
      (mixedOperator k b y α))

/--
On the actual `V_k = Sym^k(ℂ²)` carrier, reversal conjugates the diagonal
weight operator by `z ↦ z⁻¹`, and the trace of the tensor operator factors as
the product of the two weight characters.
-/
def claim14751 : Prop :=
  ∀ (k : ℕ) (b : WeightBasis k) (y α : ℂ),
    ((reversal k b).comp (diagonalWeight k b y)).comp (reversal k b) =
        diagonalWeight k b y⁻¹ ∧
      mixedTrace k b y α =
        MathlibPlus.Open.NumberTheory.Claim14746.character k y *
          MathlibPlus.Open.NumberTheory.Claim14746.character k α

/-- A ket-bra in the induced tensor-product weight basis on the actual carrier. -/
def ketBra {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid W] [Module ℂ W]
    (b : Module.Basis ι ℂ W) (p : ι) : W →ₗ[ℂ] W :=
  b.constr ℂ (fun q => if q = p then b p else 0)

/-- The equal-alignment projector `Q_{k,+}`. -/
def equalProjector (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  ∑ r : Fin (k + 1), ketBra (MixedBasis k b) (r, r)

/-- The opposite-alignment projector `Q_{k,-}`. -/
def oppositeProjector (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  ∑ r : Fin (k + 1), ketBra (MixedBasis k b) (r, Fin.rev r)

/-- The rank of a linear projector, using its actual range submodule. -/
def rangeRank {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (P : W →ₗ[ℂ] W) : ℕ :=
  Module.finrank ℂ (LinearMap.range P)

/-- The central weight index and its line in the mixed carrier. -/
def centralIndex (k : ℕ) : Fin (k + 1) :=
  ⟨k / 2, Nat.lt_succ_of_le (Nat.div_le_self k 2)⟩

def centralZeroWeightLine (k : ℕ) (b : WeightBasis k) : Submodule ℂ (M k) :=
  Submodule.span ℂ { (MixedBasis k b) (centralIndex k, centralIndex k) }

/--
The two alignment projectors have rank `k+1`; for even `k` their ranges meet
exactly in the central zero-weight line.  One-factor reversal exchanges the
two projectors, while simultaneous reversal fixes each one.
-/
def claim14752 : Prop :=
  ∀ (k : ℕ) (b : WeightBasis k),
    let Qplus := equalProjector k b
    let Qminus := oppositeProjector k b
    let Rh := leftReversal k b
    let Rc := rightReversal k b
    let D := longestOperator k b
    rangeRank Qplus = k + 1 ∧
      rangeRank Qminus = k + 1 ∧
      (Even k →
        LinearMap.range Qplus ⊓ LinearMap.range Qminus =
          centralZeroWeightLine k b) ∧
      ((Rh.comp Qplus).comp Rh = Qminus) ∧
      ((Rh.comp Qminus).comp Rh = Qplus) ∧
      ((Rc.comp Qplus).comp Rc = Qminus) ∧
      ((Rc.comp Qminus).comp Rc = Qplus) ∧
      ((D.comp Qplus).comp D = Qplus) ∧
      ((D.comp Qminus).comp D = Qminus)

end

end MathlibPlus.Open.ResearchFormalization.Claim14751_14752
