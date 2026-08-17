import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3640Claim51107

noncomputable section

private abbrev Index51107 := Fin 4
private abbrev Matrix51107 := Matrix Index51107 Index51107 ℝ

private def rMinus51107 : Matrix51107 :=
  Matrix.diagonal ![6, 3 / 2, 1 / 2, -3]

private def rPlus51107 : Matrix51107 :=
  Matrix.diagonal ![16 / 5, 3, 14 / 5, -4]

private def pencilDet51107
    (R : Matrix51107) (b : ℝ) : ℝ :=
  Matrix.det ((1 : Matrix51107) + b • R)

private def simpleRoot51107
    (R : Matrix51107) (b : ℝ) : Prop :=
  pencilDet51107 R b = 0 ∧
    deriv (pencilDet51107 R) b ≠ 0

private def inertia51107
    (R : Matrix51107) : Prop :=
  (Fintype.card {i : Index51107 // 0 < R i i} = 3) ∧
    (Fintype.card {i : Index51107 // R i i = 0} = 0) ∧
    (Fintype.card {i : Index51107 // R i i < 0} = 1)

private def rootSet51107
    (R : Matrix51107) (roots : Finset ℝ) : Prop :=
  ∀ x : ℝ, pencilDet51107 R x = 0 ↔ x ∈ roots

def claim51107 : Prop :=
  let Rminus := rMinus51107
  let Rplus := rPlus51107
  Matrix.trace Rminus = 5 ∧ Matrix.trace Rplus = 5 ∧
    inertia51107 Rminus ∧ inertia51107 Rplus ∧
    pencilDet51107 Rminus 0 = 1 ∧ pencilDet51107 Rplus 0 = 1 ∧
    rootSet51107 Rminus
      {-1 / 6, -2 / 3, -2, 1 / 3} ∧
    rootSet51107 Rplus
      {-5 / 16, -1 / 3, -5 / 14, 1 / 4} ∧
    (∀ b : ℝ,
      b ∈ ({-1 / 6, -2 / 3, -2, 1 / 3} : Finset ℝ) →
        simpleRoot51107 Rminus b) ∧
    (∀ b : ℝ,
      b ∈ ({-5 / 16, -1 / 3, -5 / 14, 1 / 4} : Finset ℝ) →
        simpleRoot51107 Rplus b) ∧
    (-1 / 6 : ℝ) < 0 ∧ (1 / 4 : ℝ) > 0 ∧
    (∀ b : ℝ, b ∈ ({-1 / 6, -2 / 3, -2, 1 / 3} : Finset ℝ) →
      |b| ≥ (1 / 6 : ℝ)) ∧
    (∀ b : ℝ, b ∈ ({-5 / 16, -1 / 3, -5 / 14, 1 / 4} : Finset ℝ) →
      |b| ≥ (1 / 4 : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.R3640Claim51107
