import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch_01a00bf2

noncomputable section

/-!
The coefficient carrier and the four operators are kept on the actual
symmetric tensor powers used by the admitted representation statements.  A
weight basis is an input datum, not a replacement by a coordinate surrogate.
-/

abbrev C2 := Fin 2 → ℂ

/-- The admitted coefficient carrier `V_k = Sym^k(ℂ²)`. -/
abbrev V (k : ℕ) := SymmetricPower ℂ (Fin k) C2

/-- The admitted mixed coefficient carrier `M_k = V_k ⊗ V_k`. -/
abbrev M (k : ℕ) := TensorProduct ℂ (V k) (V k)

/-- The weight basis `e_r` indexed by `0 ≤ r ≤ k`. -/
abbrev WeightBasis (k : ℕ) := Module.Basis (Fin (k + 1)) ℂ (V k)

/-- The induced tensor-product weight basis on `M_k`. -/
abbrev MixedBasis (k : ℕ) (b : WeightBasis k) :
    Module.Basis (Fin (k + 1) × Fin (k + 1)) ℂ (M k) :=
  b.tensorProduct b

/-- Reversal `J_k e_r = e_{k-r}` in the admitted weight basis. -/
def reversal (k : ℕ) (b : WeightBasis k) : V k →ₗ[ℂ] V k :=
  b.constr ℂ (fun r => b (Fin.rev r))

/-- Factor swap on `V_k ⊗ V_k`. -/
def factorSwap (k : ℕ) : M k →ₗ[ℂ] M k :=
  (TensorProduct.comm ℂ (V k) (V k)).toLinearMap

/-- Left long-root reversal `R_h = J_k ⊗ I`. -/
def leftReversal (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  TensorProduct.map (reversal k b) (LinearMap.id : V k →ₗ[ℂ] V k)

/-- Right long-root reversal `R_c = I ⊗ J_k`. -/
def rightReversal (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  TensorProduct.map (LinearMap.id : V k →ₗ[ℂ] V k) (reversal k b)

/-- The longest element `D = J_k ⊗ J_k`. -/
def longestOperator (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  TensorProduct.map (reversal k b) (reversal k b)

/-- The operator represented by `(s₀s₁)²` in the coefficient action. -/
def w0Operator (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  ((factorSwap k).comp (leftReversal k b)).comp
    ((factorSwap k).comp (leftReversal k b))

/-- The identity endomorphism on the mixed coefficient carrier. -/
def mixedIdentity (k : ℕ) (_b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  LinearMap.id

/-- Orthogonality in the admitted tensor weight basis.  The permutation
matrices here have real entries, so this is also their unitary condition. -/
def orthogonalInMixedBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (basis : Module.Basis ι ℂ W) (A : W →ₗ[ℂ] W) : Prop :=
  (LinearMap.toMatrix basis basis A).transpose *
      LinearMap.toMatrix basis basis A = 1

/-- The exact four distinct endomorphisms with Klein-four multiplication. -/
def isKleinFourEndomorphismSet {W : Type*}
    [AddCommMonoid W] [Module ℂ W]
    (I Rh Rc D : W →ₗ[ℂ] W) : Prop :=
  Rh.comp Rh = I ∧
    Rc.comp Rc = I ∧
    D.comp D = I ∧
    Rh.comp Rc = Rc.comp Rh ∧
    Rh.comp Rc = D ∧
    I ≠ Rh ∧ I ≠ Rc ∧ I ≠ D ∧
    Rh ≠ Rc ∧ Rh ≠ D ∧ Rc ≠ D

/-- Claim 14762: the actual `Sym^k(ℂ²) ⊗ Sym^k(ℂ²)` coefficient action has
orthogonal long-root reflections forming the named Klein four subgroup. -/
def orthogonalReflectionKleinSubgroup : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ b : WeightBasis k,
    let I := mixedIdentity k b
    let Rh := leftReversal k b
    let Rc := rightReversal k b
    let D := longestOperator k b
    isKleinFourEndomorphismSet I Rh Rc D ∧
      orthogonalInMixedBasis (MixedBasis k b) Rh ∧
      orthogonalInMixedBasis (MixedBasis k b) Rc ∧
      Rh.comp Rc = D ∧
      D = w0Operator k b

/-- `Π_+ = (I + D)/2`, the Arthur `w₀ = +1` projector. -/
def arthurProjector (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  ((2 : ℂ)⁻¹) • (mixedIdentity k b + longestOperator k b)

/-- The relative reflection `(R_h + R_c)/2`. -/
def relativeReflection (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  ((2 : ℂ)⁻¹) • (leftReversal k b + rightReversal k b)

/-- `I - Π_+`, the complementary Arthur-sector projector. -/
def complementaryArthurProjector (k : ℕ) (b : WeightBasis k) : M k →ₗ[ℂ] M k :=
  mixedIdentity k b + (-1 : ℂ) • arthurProjector k b

/-- Claim 14763: compression to the Arthur corner and the complementary-sector
sign relation, on the same actual coefficient carrier. -/
def arthurLongestElementCompression : Prop :=
  ∀ (k : ℕ), ∀ b : WeightBasis k,
    let Rh := leftReversal k b
    let Rc := rightReversal k b
    let Pi := arthurProjector k b
    let Rrel := relativeReflection k b
    let Piminus := complementaryArthurProjector k b
    Rh.comp Pi = Rrel ∧
      Rc.comp Pi = Rrel ∧
      Rrel.comp Rrel = Pi ∧
      Rc.comp Piminus = (-1 : ℂ) • (Rh.comp Piminus)

end
end MathlibPlus.Open.Research.FormalizationBatch_01a00bf2
