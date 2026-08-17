import MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

namespace MathlibPlus.Open.ResearchFormalization.R2614Claim42812

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

/-- A row can occur in a nonzero kernel determinant only if some entry in that
row is nonzero. -/
def kernelRowHasSupport {m : ℕ} (R : ℕ) (offsets : Fin m → ℤ)
    (q : Fin m → ℤ) : Prop :=
  ∀ i : Fin m, ∃ j : Fin m,
    rowUniformLaurentKernel R (q i) (offsets j) ≠ 0

/-- Claim 42812: the Laurent support interval is finite, and so are the
strict row tuples and admissible derivative cubes that can meet fixed kernel
columns at a fixed slack. -/
def claim42812 : Prop :=
  (∀ (R : ℕ) (q s : ℤ),
    0 ≤ (R : ℤ) + s - 1 →
      rowUniformLaurentKernel R q s ≠ 0 →
        s ≤ q ∧ q ≤ (R : ℤ) + 2 * s) ∧
    (∀ (m R : ℕ) (offsets : Fin m → ℤ),
      (∀ j : Fin m, 0 ≤ (R : ℤ) + offsets j - 1) →
        Set.Finite {q : Fin m → ℤ |
          StrictMono q ∧ kernelRowHasSupport R offsets q} ∧
        Set.Finite {qI : (Fin m → ℤ) × Finset (Fin m) |
          admissibleKernelCube qI.1 qI.2 ∧
            kernelRowHasSupport R offsets qI.1})



end

end MathlibPlus.Open.ResearchFormalization.R2614Claim42812
