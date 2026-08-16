import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0096e_5a75_7fe3_bebc_178cf02aa479

namespace MathlibPlus.Open.ResearchFormalization.O0140

open MathlibPlus.Open.ResearchFormalizationBatch_01a0096e_5a75_7fe3_bebc_178cf02aa479

noncomputable section

/-- The two-dimensional irreducible `rho₂`, in the induced basis used by the
central-longest-element calculation. -/
def rhoTwoS0 : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = j then if i = 0 then 1 else -1 else 0

def rhoTwoS1 : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1
  else if i = 1 ∧ j = 0 then 1
  else 0

/-- The source `rho₂ ⊕ rho₂`, with the same two Weyl generators on each
summand. -/
abbrev CentralSource := (Fin 2 ⊕ Fin 2) → ℂ

def centralSourceS0Matrix :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks rhoTwoS0 0 0 rhoTwoS0

def centralSourceS1Matrix :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks rhoTwoS1 0 0 rhoTwoS1

def centralSourceS0 : CentralSource →ₗ[ℂ] CentralSource :=
  Matrix.mulVecLin centralSourceS0Matrix

def centralSourceS1 : CentralSource →ₗ[ℂ] CentralSource :=
  Matrix.mulVecLin centralSourceS1Matrix

/-- The exact coefficient carrier `M_k = Sym^k(C²) ⊗ Sym^k(C²)` in its
standard weight-coordinate basis. -/
abbrev CentralTarget (k : ℕ) := (Fin (k + 1) × Fin (k + 1)) → ℂ

def centralTargetS0 (k : ℕ) : CentralTarget k →ₗ[ℂ] CentralTarget k :=
  Matrix.mulVecLin (swapMatrix k)

def centralTargetS1 (k : ℕ) : CentralTarget k →ₗ[ℂ] CentralTarget k :=
  Matrix.mulVecLin (rhMatrixAt k)

def centralTargetW0 (k : ℕ) : CentralTarget k →ₗ[ℂ] CentralTarget k :=
  Matrix.mulVecLin (rhMatrixAt k * rcMatrixAt k)

/-- A linear map is a `W(C₂)` intertwiner when it commutes with the two
specified Coxeter generators. -/
def centralIntertwiner
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (a0 a1 : W →ₗ[ℂ] W) (F : CentralSource →ₗ[ℂ] W) : Prop :=
  F.comp centralSourceS0 = a0.comp F ∧
    F.comp centralSourceS1 = a1.comp F

def centralTargetIntertwiner (k : ℕ)
    (F : CentralSource →ₗ[ℂ] CentralTarget k) : Prop :=
  centralIntertwiner (centralTargetS0 k) (centralTargetS1 k) F

/-- The parity indicator `j` in the exact multiplicity formula. -/
def centralParity (k : ℕ) : ℕ :=
  if k % 2 = 0 then 1 else 0

/-- The exact multiplicity of the two-dimensional irreducible in `M_k`. -/
def centralRhoMultiplicity (k : ℕ) : ℕ :=
  ((k + 1) ^ 2 - (centralParity k) ^ 2) / 4

/-- The `w₀=+1` Arthur sector of the concrete coefficient module. -/
def centralArthurProjector (k : ℕ) :
    CentralTarget k →ₗ[ℂ] CentralTarget k :=
  (1 / 2 : ℂ) • (LinearMap.id + centralTargetW0 k)

def centralArthurSector (k : ℕ) : Submodule ℂ (CentralTarget k) :=
  LinearMap.range (centralArthurProjector k)

/-- A scalar action used for a one-dimensional character line. -/
def centralScalarAction (a : ℂ) : ℂ →ₗ[ℂ] ℂ :=
  a • LinearMap.id

/-- The relative-current character line `χ_(+,-)`. -/
def centralRelativeCurrentIntertwiner
    (F : CentralSource →ₗ[ℂ] ℂ) : Prop :=
  centralIntertwiner (centralScalarAction 1) (centralScalarAction (-1)) F

/-- Exact meaning of maximum image rank for intertwiners from the source. -/
def centralMaximumImageRank (k r : ℕ) : Prop :=
  (∀ F : CentralSource →ₗ[ℂ] CentralTarget k,
      centralTargetIntertwiner k F →
        Module.finrank ℂ (LinearMap.range F) ≤ r) ∧
    (∃ F : CentralSource →ₗ[ℂ] CentralTarget k,
      centralTargetIntertwiner k F ∧
        Module.finrank ℂ (LinearMap.range F) = r)

/-- Claim 14734: the source `rho₂ ⊕ rho₂` has maximum image rank
`2 min(2,m_rho(k))`, with the stated low-degree values, while its Hom to
both the concrete Arthur sector and the relative-current line is zero. -/
def centralSourceRankAndHomObstruction_claim14734 : Prop :=
  (∀ k : ℕ,
    centralMaximumImageRank k
      (2 * min 2 (centralRhoMultiplicity k))) ∧
    centralMaximumImageRank 1 2 ∧
    (∀ k : ℕ, 2 ≤ k → centralMaximumImageRank k 4) ∧
    (∀ k : ℕ,
      ∀ F : CentralSource →ₗ[ℂ] CentralTarget k,
        centralTargetIntertwiner k F →
          LinearMap.range F ≤ centralArthurSector k →
          F = 0) ∧
    (∀ F : CentralSource →ₗ[ℂ] ℂ,
      centralRelativeCurrentIntertwiner F → F = 0)

end
end MathlibPlus.Open.ResearchFormalization.O0140
