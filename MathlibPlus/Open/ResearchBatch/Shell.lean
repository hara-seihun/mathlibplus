import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Shell

open scoped BigOperators

noncomputable section

abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Matrix action on a finite real vector. -/
def applyMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Vec n :=
  fun i => ∑ j, A i j * x j

/-- Symmetry of a real shell matrix. -/
def MatrixSymmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = A j i

/-- The standard symplectic form on a pair of shell vectors. -/
def standardSymplecticForm {n : ℕ}
    (u v : Vec n × Vec n) : ℝ :=
  (∑ i, u.1 i * v.2 i) - ∑ i, u.2 i * v.1 i

/-- The lower-block shell shear. -/
def shellShear {n : ℕ} (Δ : Matrix (Fin n) (Fin n) ℝ)
    (u : Vec n × Vec n) : Vec n × Vec n :=
  (u.1, applyMatrix Δ u.1 + u.2)

/-- Symplecticity expressed by preservation of the standard form. -/
def IsSymplecticShear {n : ℕ} (Δ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u v,
    standardSymplecticForm (shellShear Δ u) (shellShear Δ v) =
      standardSymplecticForm u v

/-- Lagrangian graph of a matrix. -/
def lagrangianGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Set (Vec n × Vec n) :=
  {u | u.2 = applyMatrix A u.1}

/-- Shell addition is the symplectic shear sending graph `A` to graph
`A + Δ`. -/
def shellAdditionAsSymplecticShear : Prop :=
  ∀ (n : ℕ) (A Δ : Matrix (Fin n) (Fin n) ℝ),
    MatrixSymmetric Δ →
      IsSymplecticShear Δ ∧
        shellShear Δ '' lagrangianGraph A = lagrangianGraph (A + Δ)

/-- The rank-attachment path as an operator on the shell plus one new
coordinate. -/
def rankAttachmentOperator {n : ℕ}
    (A Δ : Matrix (Fin n) (Fin n) ℝ) (q : Vec n) (β t : ℝ)
    (u : Vec n × ℝ) : Vec n × ℝ :=
  (applyMatrix (A + t • Δ) u.1 + (t * u.2) • q,
    t * (∑ i, q i * u.1 i) + t * β * u.2)

/-- Specification of the displayed rank-attachment block path. -/
def rankAttachmentPathSpecification {n : ℕ}
    (A Δ : Matrix (Fin n) (Fin n) ℝ) (q : Vec n) (β : ℝ)
    (H : ℝ → (Vec n × ℝ) → (Vec n × ℝ)) : Prop :=
  ∀ t u, H t u = rankAttachmentOperator A Δ q β t u

/-- A two-sided inverse relation for a finite square matrix. -/
def IsMatrixInverse {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i k, ∑ j, A i j * B j k = if i = k then 1 else 0) ∧
    (∀ i k, ∑ j, B i j * A j k = if i = k then 1 else 0)

/-- The Schur flux of the terminal rank attachment. -/
def terminalSchurFlux {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (q : Vec n) (β : ℝ) : ℝ :=
  β - ∑ i, q i * applyMatrix B q i

/-- The displayed terminal Schur-complement formula, with `B` the inverse of
`Aplus`. -/
def terminalSchurFluxFormula {n : ℕ}
    (Aplus B : Matrix (Fin n) (Fin n) ℝ) (q : Vec n) (β σ : ℝ) : Prop :=
  IsMatrixInverse Aplus B → σ = terminalSchurFlux B q β

/-- Positive definiteness of a finite real matrix viewed as a quadratic form. -/
def PositiveDefiniteMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Vec n, x ≠ 0 → 0 < ∑ i, x i * applyMatrix A x i

/-- Positive definiteness of the shell-plus-one-coordinate operator. -/
def PositiveDefiniteAttachment {n : ℕ}
    (H : (Vec n × ℝ) → (Vec n × ℝ)) : Prop :=
  ∀ u, u ≠ 0 →
    0 < (∑ i, u.1 i * (H u).1 i) + u.2 * (H u).2

/-- Schur's positive-definite attachment criterion. -/
def positiveDefiniteAttachmentIffFlux : Prop :=
  ∀ (n : ℕ) (A Δ : Matrix (Fin n) (Fin n) ℝ) (q : Vec n)
    (β : ℝ) (B : Matrix (Fin n) (Fin n) ℝ),
    MatrixSymmetric (A + Δ) →
      PositiveDefiniteMatrix (A + Δ) →
        IsMatrixInverse (A + Δ) B →
          (PositiveDefiniteAttachment (rankAttachmentOperator A Δ q β 1) ↔
            terminalSchurFlux B q β > 0)

end

end MathlibPlus.Open.ResearchBatch.Shell
