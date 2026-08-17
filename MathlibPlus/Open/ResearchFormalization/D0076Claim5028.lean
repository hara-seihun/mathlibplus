import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationD0076

noncomputable section

private def downAt
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred) :
    ∀ n : ℕ, A n →ₗ[K] A n.pred
  | 0 => 0
  | n + 1 => D (n + 1)

private def downSucc
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) : A (n + 1) →ₗ[K] A n :=
  (LinearEquiv.cast (Nat.pred_succ n)).toLinearMap.comp (D (n + 1))

private def upAt
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1)) :
    ∀ n : ℕ, A n.pred →ₗ[K] A n
  | 0 => 0
  | n + 1 => U n

private def upIterate
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1)) :
    (m k : ℕ) → A m →ₗ[K] A (m + k)
  | _m, 0 => LinearMap.id
  | m, k + 1 => (U (m + k)).comp (upIterate K A U m k)

private def transportedUp
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (n k : ℕ) (hk : k ≤ n) : A (n - k) →ₗ[K] A n :=
  (LinearEquiv.cast (Nat.sub_add_cancel hk)).toLinearMap.comp
    (upIterate K A U (n - k) k)

private def primitiveSpace
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (m : ℕ) : Submodule K (A m) :=
  LinearMap.ker (downAt K A D m)

private def primitiveSummand
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) (k : {j : ℕ // j ≤ n}) : Submodule K (A n) :=
  Submodule.map
    (transportedUp K A U n k.1 k.2)
    (primitiveSpace K A D (n - k.1))

private def previousFinrank
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    : ℕ → ℕ
  | 0 => 0
  | n + 1 => Module.finrank K (A n)

private def udOperator
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) : A n →ₗ[K] A n :=
  (upAt K A U n).comp (D n)

private def gaugedUp
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (a : ℕ → K) (n : ℕ) : A n →ₗ[K] A (n + 1) :=
  (a n) • U n

private def gaugedDown
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (b : ℕ → K) (n : ℕ) : A n →ₗ[K] A n.pred :=
  (b n) • D n

private def udScale
    (K : Type*) [Field K] (a b : ℕ → K) : ℕ → K
  | 0 => 1
  | n + 1 => b (n + 1) * a n

private def primitivePackage
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    [∀ n : ℕ, FiniteDimensional K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) : Prop :=
  DirectSum.IsInternal (primitiveSummand K A U D n) ∧
    (∀ k : {j : ℕ // j ≤ n},
      ∃ μ : K,
        primitiveSummand K A U D n k =
          Module.End.eigenspace (udOperator K A U D n) μ) ∧
    Module.finrank K (primitiveSpace K A D n) =
      Module.finrank K (A n) - previousFinrank K A n

/-- Claim 5028: a nonvanishing graded up-down pair keeps injectivity,
surjectivity, the complete primitive direct-sum/eigenspace package, and the
primitive summands under every nonzero level-wise grading gauge, while the
numerical eigenvalues of the level-wise `UD` operator are rescaled. -/
def claim5028 : Prop :=
  ∀ (K : Type*) [Field K]
    (A : ℕ → Type*)
    [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    [∀ n : ℕ, FiniteDimensional K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (q : Kˣ)
    (r : ℕ → K),
    (∀ n : ℕ,
      (downSucc K A D n).comp (U n) -
          (q : K) • (upAt K A U n).comp (D n) =
        (r n) • (LinearMap.id : A n →ₗ[K] A n)) →
    (∀ n : ℕ, r n ≠ 0) →
    ∀ (a b : ℕ → K),
      (∀ n : ℕ, a n ≠ 0) →
      (∀ n : ℕ, b n ≠ 0) →
      let U' : ∀ n : ℕ, A n →ₗ[K] A (n + 1) := gaugedUp K A U a
      let D' : ∀ n : ℕ, A n →ₗ[K] A n.pred := gaugedDown K A D b
      let udScale' : ℕ → K := udScale K a b
      (∀ n : ℕ,
        Function.Injective (U n) ∧ Function.Injective (U' n)) ∧
      (∀ n : ℕ,
        Function.Surjective (downSucc K A D n) ∧
          Function.Surjective (downSucc K A D' n)) ∧
      (∀ n : ℕ,
        primitiveSpace K A D n = primitiveSpace K A D' n) ∧
      (∀ n : ℕ,
        Module.finrank K (primitiveSpace K A D n) =
            Module.finrank K (A n) - previousFinrank K A n ∧
          Module.finrank K (primitiveSpace K A D' n) =
            Module.finrank K (A n) - previousFinrank K A n) ∧
      (∀ (n : ℕ) (k : {j : ℕ // j ≤ n}),
        primitiveSummand K A U D n k =
          primitiveSummand K A U' D' n k) ∧
      (∀ n : ℕ,
        primitivePackage K A U D n ∧
          primitivePackage K A U' D' n) ∧
      (∀ (n : ℕ) (μ : K),
        Module.End.eigenspace (udOperator K A U D n) μ =
          Module.End.eigenspace (udOperator K A U' D' n)
            (udScale' n * μ)) ∧
      (∀ (n : ℕ) (μ c : K),
        (∃ x : A (n + 1), x ≠ 0 ∧
          udOperator K A U D (n + 1) x = μ • x) →
        μ ≠ 0 → c ≠ 0 → c * μ ≠ μ →
        ∃ a' b' : ℕ → K,
          (∀ j : ℕ, a' j ≠ 0 ∧ b' j ≠ 0) ∧
          b' (n + 1) * a' n = c ∧
          Module.End.eigenspace (udOperator K A U D (n + 1)) μ =
            Module.End.eigenspace
              (udOperator K A (gaugedUp K A U a')
                (gaugedDown K A D b') (n + 1)) (c * μ))

end

end MathlibPlus.Open.ResearchFormalizationD0076
