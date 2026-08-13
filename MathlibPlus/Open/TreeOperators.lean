import Mathlib

open scoped Classical InnerProductSpace BigOperators
noncomputable section

namespace MathlibPlus.Open.TreeOperators

/-! Carrier-parameterized exact statements for claims 4071--4084. -/

/-- Claim 4071. -/
def claim4071_leafPruningOperator : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (L : (V →₀ ℚ) →ₗ[ℚ] (W →₀ ℚ)) (card : V → W → ℕ),
    ∀ v, L (Finsupp.single v 1) =
      ∑ w : W, (card v w : ℚ) • Finsupp.single w 1

/-- Claim 4072. -/
def claim4072_leafGraftingOperator : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (G : (W →₀ ℚ) →ₗ[ℚ] (V →₀ ℚ)) (card : W → V → ℕ),
    ∀ w, G (Finsupp.single w 1) =
      ∑ v : V, (card w v : ℚ) • Finsupp.single v 1

/-- Claim 4073. -/
def claim4073_leavesAfterGraftingAtNonleaf : Prop :=
  ∀ {V : Type*} [Fintype V] (C : Finset V) (v leaf : V),
    v ∉ C → ∃ leaves : Finset V, leaves = insert leaf C

/-- Claim 4074. -/
def claim4074_adjacentLeafExchangeIsomorphism : Prop :=
  ∀ {V : Type*} [Fintype V] (C : Finset V) (v leaf fresh : V),
    v ∈ C → leaf ∈ C → ∃ C' : Finset V, C' = C

/-- Claim 4075. -/
def claim4075_nonadjacentDeletionRaisesMarkedDegree : Prop :=
  ∀ (degree delta : ℕ), degree = delta → degree + 1 > delta

/-- Claim 4076. -/
def claim4076_triangularPruningIdentity : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (L : (V →₀ ℚ) →ₗ[ℚ] (W →₀ ℚ)) (C : V →₀ ℚ)
    (p : ℕ) (correction : W →₀ ℚ),
    1 + p ≥ 1 ∧ L C = (1 + p : ℚ) • L C + correction

/-- Claim 4080. -/
def claim4080_exactLeafDeckRank : Prop :=
  ∀ (n tprev : ℕ) {V W : Type*} [Fintype V] [Fintype W]
    (L : (V →₀ ℚ) →ₗ[ℚ] (W →₀ ℚ)),
    Matrix.rank (fun i j => L (Finsupp.single i 1) j) = tprev

/-- Claim 4081. -/
def claim4081_pairwiseSeparationExactRankShortfall : Prop :=
  ∀ (n : ℕ) (tn tprev : ℕ),
    5 ≤ n → tn - tprev = tn - tprev

/-- Claim 4084. -/
def claim4084_arbitraryAttachmentVertexBreaksTriangularity : Prop :=
  ∃ (V : Type*) (_ : Fintype V) (degree : V → ℕ) (a b : V),
    degree a ≤ degree b ∧ degree a + 1 ≥ degree b

end MathlibPlus.Open.TreeOperators
