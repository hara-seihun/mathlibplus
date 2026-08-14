import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.MatrixChannels

/-- A selected-column presentation uses the selected coordinates followed by the
remaining coordinates.  The field `inverse` records the chosen inverse of the
selected square block. -/
structure BlockPresentation (𝕜 : Type*) [Field 𝕜] (m k : ℕ) where
  A : Matrix (Fin m) (Fin m ⊕ Fin k) 𝕜
  inverse : Matrix (Fin m) (Fin m) 𝕜
  fullRowRank : Matrix.rank A = m
  leftInverse :
    inverse * (show Matrix (Fin m) (Fin m) 𝕜 from fun i j => A i (Sum.inl j)) =
      (1 : Matrix (Fin m) (Fin m) 𝕜)
  rightInverse :
    (show Matrix (Fin m) (Fin m) 𝕜 from fun i j => A i (Sum.inl j)) * inverse =
      (1 : Matrix (Fin m) (Fin m) 𝕜)

abbrev SelectedBlock {𝕜 : Type*} [Field 𝕜] {m k : ℕ}
    (P : BlockPresentation 𝕜 m k) := Matrix (Fin m) (Fin m) 𝕜

abbrev UnselectedBlock {𝕜 : Type*} [Field 𝕜] {m k : ℕ}
    (P : BlockPresentation 𝕜 m k) := Matrix (Fin m) (Fin k) 𝕜

def selectedBlock {𝕜 : Type*} [Field 𝕜] {m k : ℕ}
    (P : BlockPresentation 𝕜 m k) : SelectedBlock P :=
  fun i j => P.A i (Sum.inl j)

def unselectedBlock {𝕜 : Type*} [Field 𝕜] {m k : ℕ}
    (P : BlockPresentation 𝕜 m k) : UnselectedBlock P :=
  fun i j => P.A i (Sum.inr j)

/-- The matrix `K=A_S⁻¹ A_U` in selected/unselected coordinates. -/
def quotientMatrix {𝕜 : Type*} [Field 𝕜] {m k : ℕ}
    (P : BlockPresentation 𝕜 m k) : Matrix (Fin m) (Fin k) 𝕜 :=
  P.inverse * unselectedBlock P

def blockVector {α : Type*} {m k : ℕ} [Zero α]
    (x : Fin m → α) (y : Fin k → α) : Fin m ⊕ Fin k → α
  | Sum.inl i => x i
  | Sum.inr j => y j

/-- Every kernel vector has the selected/unselected parametrization
`(-K x,x)`, with uniqueness of the unselected coordinate. -/
def kernel_unique_parametrization : Prop :=
  ∀ (𝕜 : Type*) [Field 𝕜] (m k : ℕ)
    (P : BlockPresentation 𝕜 m k)
    (z : Fin m ⊕ Fin k → 𝕜),
    P.A.mulVec z = 0 ↔
      ∃! x : Fin k → 𝕜,
        z = blockVector (-(quotientMatrix P).mulVec x) x

end MathlibPlus.Open.ResearchFormalization.MatrixChannels
