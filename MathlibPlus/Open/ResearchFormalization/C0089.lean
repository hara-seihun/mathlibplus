import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0089

/-- The prime-counting function on real inputs, using the natural floor. -/
noncomputable def primeCounting (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ)

/-- Pole-cancelled prime-counting score from the admitted repair context. -/
noncomputable def B (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / primeCounting x)

/-- The endpoint value β(N)=B(N-1). -/
noncomputable def beta (N : ℕ) : ℝ := B ((N : ℝ) - 1)

/-- A displayed point realizes the maximum of B on the tail x≥N. -/
def realizesTailMaximum (N : ℕ) (x : ℝ) : Prop :=
  (N : ℝ) ≤ x ∧ ∀ y : ℝ, (N : ℝ) ≤ y → B y ≤ B x

/-- A coefficient and its two endpoint values describe one bottom cell. -/
def bottomCell
    (c : ℝ) (N : ℕ) (alphaPoint : ℝ)
    (alphaLower alphaUpper betaLower betaUpper : ℝ) : Prop :=
  realizesTailMaximum N alphaPoint ∧
    alphaLower < B alphaPoint ∧ B alphaPoint < alphaUpper ∧
    betaLower < beta N ∧ beta N < betaUpper ∧
    B alphaPoint < c ∧ c ≤ beta N

/-- Three explicit bottom cells and their admitted endpoint intervals. -/
def threeExplicitBottomCells : Prop :=
  bottomCell
    (1.149 : ℝ) 42575222505 (42575222505 : ℝ)
    (1.14899999978948990672 : ℝ) (1.14899999978948990673 : ℝ)
    (1.14900001268097863821 : ℝ) (1.14900001268097863822 : ℝ) ∧
  bottomCell
    (1.15 : ℝ) 38284442297 (38284442321 : ℝ)
    (1.14999999231912774956 : ℝ) (1.14999999231912774957 : ℝ)
    (1.15000000129706374421 : ℝ) (1.15000000129706374422 : ℝ) ∧
  bottomCell
    (1.14900031 : ℝ) 42575222481 (42575222481 : ℝ)
    (1.14900030918521945190 : ℝ) (1.14900030918521945191 : ℝ)
    (1.14900032207670818247 : ℝ) (1.14900032207670818248 : ℝ)

end MathlibPlus.Open.ResearchFormalization.C0089
