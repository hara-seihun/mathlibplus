import MathlibPlus.Open.ResearchFormalization.R0324IsolateFreePrimitive

namespace MathlibPlus.Open.ResearchFormalization.R0324Claim19864

open MathlibPlus.Open.ResearchFormalization.R0324HomogeneousDeckKernels
open MathlibPlus.Open.ResearchFormalization.R0324IsolateFreePrimitive
open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

private def primitiveSubmodule (n r : ℕ) :
    Submodule ℚ (GraphSpace n) :=
  Submodule.span ℚ (isolateFreePrimitiveVectors n r)

private def edgeRaiseLinear (n : ℕ) : ℕ →
    GraphSpace n →ₗ[ℚ] GraphSpace n
  | 0 => LinearMap.id
  | q + 1 => (edgeAdditionOperator n).comp (edgeRaiseLinear n q)

private def raisedPrimitiveSubmodule (n k r : ℕ) :
    Submodule ℚ (GraphSpace n) :=
  Submodule.map (edgeRaiseLinear n (k - r)) (primitiveSubmodule n r)

private def decompositionSubmodule (n k : ℕ) :
    Submodule ℚ (GraphSpace n) :=
  let M := Nat.choose n 2
  (Finset.Icc 0 (min k (M - k))).sup
    (fun r => raisedPrimitiveSubmodule n k r)

private def primitiveDecompositionPredicate (n k : ℕ)
    (x : GraphSpace n)
    (p : Fin (min k (Nat.choose n 2 - k) + 1) → GraphSpace n) : Prop :=
  (∀ r : Fin (min k (Nat.choose n 2 - k) + 1),
    p r ∈ isolateFreePrimitiveVectors n r.val) ∧
    x = ∑ r : Fin (min k (Nat.choose n 2 - k) + 1),
      edgeRaiseLinear n (k - r.val) (p r)

/-- The restricted edge-Lefschetz decomposition, with the graph order and
edge-rank range explicitly restricted to `0 ≤ k ≤ binom(n,2)`. -/
def restrictedLefschetzDecomposition_claim19864 : Prop :=
  ∀ (n k : ℕ),
    k ≤ Nat.choose n 2 →
      homogeneousDeckKernel n k =
          {x | x ∈ decompositionSubmodule n k} ∧
        ∀ x : GraphSpace n, x ∈ homogeneousDeckKernel n k →
          ∃! p : Fin (min k (Nat.choose n 2 - k) + 1) → GraphSpace n,
            primitiveDecompositionPredicate n k x p

end

end MathlibPlus.Open.ResearchFormalization.R0324Claim19864
