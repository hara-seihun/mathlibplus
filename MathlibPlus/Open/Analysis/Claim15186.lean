import MathlibPlus.Open.Analysis.Claim15188

open scoped BigOperators Matrix

namespace MathlibPlus.Open.Analysis.Claim15186

noncomputable section

open MathlibPlus.Open.Analysis.Claim15188

/--
The scalar finite-section carrier for the rank-one Uvarov update.  The vector
`v` is indexed by the monomial coefficients, and `M` is the actual updated
Hankel section rather than an unconstrained matrix callback.
-/
def formalUvarovPolynomialFormula_claim15186 : Prop :=
  ∀ (n : ℕ) (α : ℝ) (μ v h : ℕ → ℝ)
    (π : ℕ → Polynomial ℝ),
    let H : ∀ m : ℕ, Matrix (Fin m) (Fin m) ℝ :=
      fun m => hankelSection μ m
    let M : ∀ m : ℕ, Matrix (Fin m) (Fin m) ℝ :=
      fun m => fun i j => H m i j + α * v i.1 * v j.1
    let lambda : ℕ → ℝ := fun k => uvarovLambda v π k
    let eta : ℕ → ℝ := fun m => uvarovEta α v h π m
    let hhat : ℝ := h n + α * lambda n ^ 2 / eta n
    (∀ k : ℕ, k ≤ n →
      (π k).Monic ∧
        (π k).natDegree = k ∧
        Matrix.det (H (k + 1)) ≠ 0 ∧
        h k ≠ 0 ∧
        H (k + 1) *ᵥ coefficientVector (k + 1) (π k) =
          terminalVector k (h k)) →
    eta n ≠ 0 →
    ∃ πhat : Polynomial ℝ,
      πhat.Monic ∧
        πhat.natDegree = n ∧
        M (n + 1) *ᵥ coefficientVector (n + 1) πhat =
          terminalVector n hhat ∧
        πhat = updatedExtremal α v h π n

end

end MathlibPlus.Open.Analysis.Claim15186
