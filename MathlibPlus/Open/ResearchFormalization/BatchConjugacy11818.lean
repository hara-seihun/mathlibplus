import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchConjugacy11818

noncomputable section

open scoped BigOperators

/-- The degree-one reciprocal-pair representation on `ℂ²`. -/
def DOne (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then z else z⁻¹)

/-- The `V₁ ⊗ V₁` operator carrying the four local weights. -/
def TOne (y α : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => DOne y i.1 j.1 * DOne α i.2 j.2

/-- The equal-alignment and opposite-alignment projectors in `V₁ ⊗ V₁`. -/
def QPlus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i.1 = i.2 then 1 else 0)

def QMinus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i.1.val + i.2.val = 1 then 1 else 0)

/-- The trace of `TOne` after insertion of an alignment projector. -/
def insertedTrace (y α : ℂ)
    (Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    TOne y α i j * Q j i

/-- The four-weight ordinary `GL₄` local factor attached to `TOne`. -/
def ordinaryGL4Factor (y α X : ℂ) : ℂ :=
  ∏ i : Fin 2 × Fin 2, (1 - TOne y α i i * X)

def reciprocalTrace (z : ℂ) : ℂ := z + z⁻¹

def AData (y : ℂ) : ℂ := y + y⁻¹

def BData (α : ℂ) : ℂ := α + α⁻¹

def orientationData (y α : ℂ) : ℂ := (y - y⁻¹) * (α - α⁻¹)

def rOne (y α : ℂ) : ℂ := insertedTrace y α QPlus

def rTwo (y α : ℂ) : ℂ := insertedTrace y α QMinus

/-- At degree one, ordinary conjugacy data retain the square but not the
orientation sign of the two reciprocal-pair traces. -/
def conjugacyDataDeterminesOnlySquare : Prop :=
  ∀ y α : ℂ, y ≠ 0 → α ≠ 0 →
    (rOne y α + rTwo y α = AData y * BData α) ∧
    (rOne y α - rTwo y α = orientationData y α) ∧
    (orientationData y α)^2 =
      ((AData y)^2 - 4) * ((BData α)^2 - 4) ∧
    (∀ X : ℂ,
      ordinaryGL4Factor y α X =
        1 - (AData y * BData α) * X +
          ((AData y)^2 + (BData α)^2 - 2) * X^2 -
          (AData y * BData α) * X^3 + X^4) ∧
    (∀ X : ℂ, ordinaryGL4Factor y α X = ordinaryGL4Factor y α⁻¹ X) ∧
    (BData (α⁻¹) = BData α) ∧
    (rOne y (α⁻¹) = rTwo y α) ∧
    (rTwo y (α⁻¹) = rOne y α) ∧
    (orientationData y (α⁻¹) = -orientationData y α)

end

end MathlibPlus.Open.ResearchFormalization.BatchConjugacy11818
