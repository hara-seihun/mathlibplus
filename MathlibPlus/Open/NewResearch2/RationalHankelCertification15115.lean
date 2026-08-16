import MathlibPlus.Open.NewResearch2.RationalHankel15104_15107

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.RationalHankelCertification15115

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankelStructure

/-- The Euclidean norm on a finite complex vector. -/
def euclideanNorm {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The induced Euclidean/operator 2-norm of a finite complex matrix. -/
noncomputable def operatorNorm2 {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ℝ :=
  sSup {s : ℝ | ∃ x : n → ℂ,
    euclideanNorm x = 1 ∧ s = euclideanNorm (M.mulVec x)}

/-- The block-Hankel window beginning at `n₀`; its entry block is
`c (n₀ + i + j + ν)`, on the exact `(Fin L × Fin d) × Fin K` carrier. -/
def windowBlockHankel {d L K : ℕ} (c : ℕ → Fin d → ℂ)
    (n₀ ν : ℕ) : Matrix (Fin L × Fin d) (Fin K) ℂ :=
  blockHankel (fun n i => c (n₀ + n) i) ν

/-- Finite block-Hankel perturbation bound: coefficientwise vector errors are
controlled by the displayed Euclidean error budget, and the squared budget is
kept as an explicit conclusion. -/
def claim_15115 : Prop :=
  ∀ (d L K n₀ ν : ℕ)
    (cR ctilde : ℕ → Fin d → ℂ) (ε : ℕ → ℝ),
    (∀ n : ℕ,
      0 ≤ ε n ∧
        euclideanNorm (fun i : Fin d => ctilde n i - cR n i) ≤ ε n) →
    let HR := windowBlockHankel (L := L) (K := K) cR n₀ ν
    let Htilde := windowBlockHankel (L := L) (K := K) ctilde n₀ ν
    let ην := Real.sqrt
      (∑ i : Fin L, ∑ j : Fin K,
        ε (n₀ + i.val + j.val + ν) ^ 2)
    operatorNorm2 (Htilde - HR) ≤ ην ∧
      ην ^ 2 = ∑ i : Fin L, ∑ j : Fin K,
        ε (n₀ + i.val + j.val + ν) ^ 2

end
end MathlibPlus.Open.NewResearch2.RationalHankelCertification15115
