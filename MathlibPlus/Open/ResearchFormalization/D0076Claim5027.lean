import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationD0076

noncomputable section

private def claim5027DownAt
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred) :
    ∀ n : ℕ, A n →ₗ[K] A n.pred
  | 0 => 0
  | n + 1 => D (n + 1)

private def claim5027DownSucc
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) : A (n + 1) →ₗ[K] A n :=
  (LinearEquiv.cast (Nat.pred_succ n)).toLinearMap.comp (D (n + 1))

private def claim5027UpAt
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1)) :
    ∀ n : ℕ, A n.pred →ₗ[K] A n
  | 0 => 0
  | n + 1 => U n

private def claim5027UpIterate
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1)) :
    (m k : ℕ) → A m →ₗ[K] A (m + k)
  | _m, 0 => LinearMap.id
  | m, k + 1 => (U (m + k)).comp (claim5027UpIterate K A U m k)

private def claim5027TransportedUp
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (n k : ℕ) (hk : k ≤ n) : A (n - k) →ₗ[K] A n :=
  (LinearEquiv.cast (Nat.sub_add_cancel hk)).toLinearMap.comp
    (claim5027UpIterate K A U (n - k) k)

private def claim5027PrimitiveSpace
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (m : ℕ) : Submodule K (A m) :=
  LinearMap.ker (claim5027DownAt K A D m)

private def claim5027PrimitiveSummand
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) (k : {j : ℕ // j ≤ n}) : Submodule K (A n) :=
  Submodule.map
    (claim5027TransportedUp K A U n k.1 k.2)
    (claim5027PrimitiveSpace K A D (n - k.1))

private def claim5027PreviousFinrank
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)] :
    ℕ → ℕ
  | 0 => 0
  | n + 1 => Module.finrank K (A n)

private def claim5027UDOperator
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) : A n →ₗ[K] A n :=
  (claim5027UpAt K A U n).comp (D n)

private def claim5027PrimitivePackage
    (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n : ℕ, AddCommGroup (A n)]
    [∀ n : ℕ, Module K (A n)]
    [∀ n : ℕ, FiniteDimensional K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A n →ₗ[K] A n.pred)
    (n : ℕ) : Prop :=
  DirectSum.IsInternal (claim5027PrimitiveSummand K A U D n) ∧
    (∀ k : {j : ℕ // j ≤ n},
      ∃ μ : K,
        claim5027PrimitiveSummand K A U D n k =
          Module.End.eigenspace (claim5027UDOperator K A U D n) μ) ∧
    Module.finrank K (claim5027PrimitiveSpace K A D n) =
      Module.finrank K (A n) - claim5027PreviousFinrank K A n

/-- The nonvanishing graded up-down pair has the primitive direct-sum and
UD-eigenspace package at every level. -/
def claim5027 : Prop :=
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
      (claim5027DownSucc K A D n).comp (U n) -
          (q : K) • (claim5027UpAt K A U n).comp (D n) =
        (r n) • (LinearMap.id : A n →ₗ[K] A n)) →
    (∀ n : ℕ, r n ≠ 0) →
    (∀ n : ℕ, Function.Injective (U n)) ∧
      (∀ n : ℕ, Function.Surjective (claim5027DownSucc K A D n)) ∧
      (∀ n : ℕ, claim5027PrimitivePackage K A U D n)

end

end MathlibPlus.Open.ResearchFormalizationD0076
