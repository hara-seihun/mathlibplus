import MathlibPlus.Open.Analysis.Claim15192
import MathlibPlus.Analysis.Claim15187

open scoped BigOperators Matrix

namespace MathlibPlus.Open.Analysis.Claim15190

noncomputable section

open MathlibPlus.Open.Analysis.Claim15188
open MathlibPlus.Open.Analysis.Claim15192

/-- The scalar active Hankel/Uvarov hypotheses through a finite section. -/
def scalarActiveSectionData (n : ℕ) (P C : Polynomial ℝ) (α : ℝ)
    (π : ℕ → Polynomial ℝ) (h : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, k ≤ n →
    (π k).Monic ∧
      (π k).natDegree = k ∧
        Matrix.det (activeHankel P (k + 1)) ≠ 0 ∧
          h k ≠ 0 ∧
            activeHankel P (k + 1) *ᵥ coefficientVector (k + 1) (π k) =
              terminalVector k (h k)

/-- The actual Schur-complement terminal pivot of the Toeplitz-congruent
active kernel.  The leading block is required only to be nonsingular, not
positive definite. -/
noncomputable def activeTerminalPivot (n : ℕ) (P C : Polynomial ℝ) (α : ℝ) : ℝ :=
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    activeKernelSection P C α (n + 1)
  let K : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => G i.castSucc j.castSucc
  let b : Fin n → ℝ := fun i => G i.castSucc (Fin.last n)
  let c : ℝ := G (Fin.last n) (Fin.last n)
  c - b ⬝ᵥ (K⁻¹ *ᵥ b)

/-- The finite active-pivot carrier at rank `n`: the updated polynomial,
updated Hankel equation, nonsingular updated section, and the nonsingular
leading Schur block are all attached to the actual `P,C,alpha` kernel. -/
def activePivotSectionData (n : ℕ) (P C : Polynomial ℝ) (α : ℝ)
    (π : ℕ → Polynomial ℝ) (h : ℕ → ℝ) : Prop :=
  let v : ℕ → ℝ := activeUpdateVector P C
  let η : ℕ → ℝ := uvarovEta α v h π
  let pihat : Polynomial ℝ := updatedExtremal α v h π n
  let hhat : ℝ := h n + α * uvarovLambda v π n ^ 2 / η n
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    activeUpdatedHankel P C α (n + 1)
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    activeKernelSection P C α (n + 1)
  let K : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => G i.castSucc j.castSucc
  pihat.Monic ∧
    pihat.natDegree = n ∧
      Matrix.det M ≠ 0 ∧
        M *ᵥ coefficientVector (n + 1) pihat = terminalVector n hhat ∧
          Matrix.det K ≠ 0

/-- Claim 15190: on the actual Toeplitz-congruent active kernel, the adjacent
Schur terminal-pivot ratio separates the scalar Hankel norm ratio from the
single Uvarov curvature factor.  The two pivot identifications are included
as conclusions, so the ratio is not a statement about a manufactured pivot
sequence. -/
def adjacentActivePivotFactorization_claim15190 : Prop :=
  ∀ (n : ℕ) (P C : Polynomial ℝ) (α : ℝ)
    (π : ℕ → Polynomial ℝ) (h : ℕ → ℝ),
    1 ≤ n →
    P.coeff 0 ≠ 0 →
    scalarActiveSectionData n P C α π h →
    let v : ℕ → ℝ := activeUpdateVector P C
    let η : ℕ → ℝ := uvarovEta α v h π
    η (n - 1) ≠ 0 →
    η n ≠ 0 →
    activePivotSectionData n P C α π h →
    activePivotSectionData (n - 1) P C α π h →
      (activeTerminalPivot n P C α =
          (P.coeff 0) ^ 2 * h n * (η (n + 1) / η n)) ∧
      (activeTerminalPivot (n - 1) P C α =
          (P.coeff 0) ^ 2 * h (n - 1) * (η n / η (n - 1))) ∧
      activeTerminalPivot n P C α / activeTerminalPivot (n - 1) P C α =
        (h n / h (n - 1)) *
          (η (n + 1) * η (n - 1) / η n ^ 2)

end

end MathlibPlus.Open.Analysis.Claim15190
