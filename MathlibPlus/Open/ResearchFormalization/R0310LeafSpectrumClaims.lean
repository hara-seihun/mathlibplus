import MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.R0310LeafSpectrumClaims

open scoped BigOperators
open MathlibPlus.Open.TreeSpectral

noncomputable section

/-- The lowering map after `k` graftings, transported to the typed degree
`m + (k - 1)`. -/
def loweringToPrevious (m k : ℕ)
    (h : m + k - 1 = m + (k - 1)) :
    TreeSpace (m + k) →ₗ[ℚ] TreeSpace (m + (k - 1)) :=
  (transportTreeSpace h).comp (leafDeletion (m + k))

/-- The coefficient in the iterated lowering formula. -/
def loweringCoefficient (m k : ℕ) : ℚ :=
  ((k * m + Nat.choose k 2 : ℕ) : ℚ)

/-- The same coefficient written at top degree. -/
def depthEigenvalue (n k : ℕ) : ℚ :=
  ((k * (n - k) + Nat.choose k 2 : ℕ) : ℚ)

/-- The non-exceptional grafting depths used by the admitted positive-degree
spectral statements. -/
def allowedDepth (n k : ℕ) : Prop :=
  k ≤ n ∧ 2 ≤ n - k

/-- A basis formulation of diagonalizability for a rational endomorphism. -/
def diagonalizableEndomorphism {M : Type} [AddCommGroup M] [Module ℚ M]
    (A : Module.End ℚ M) : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι ℚ M) (eigenValues : ι → ℚ),
    ∀ i : ι, A (b i) = eigenValues i • b i

/-- Claim 19635: on the exact degree-shifted tree spaces, iterated grafting
from `ker L_m` lowers with coefficient `k m + binom(k,2)`, with the stated
initial value and recursion. -/
def claim19635 : Prop :=
  (∀ (m k : ℕ) (hk : 1 ≤ k),
    ∀ v : TreeSpace m,
      v ∈ LinearMap.ker (leafDeletion m) →
        let h : m + k - 1 = m + (k - 1) := Nat.add_sub_assoc hk m
        loweringToPrevious m k h (graftPow m k v) =
            loweringCoefficient m k • graftPow m (k - 1) v) ∧
    (∀ m : ℕ, loweringCoefficient m 1 = (m : ℚ)) ∧
    (∀ (m j : ℕ), 1 ≤ j →
      loweringCoefficient m (j + 1) =
        loweringCoefficient m j + (m : ℚ) + (j : ℚ))

/-- Claim 19636: the positive-degree `GL` endomorphism is diagonalizable, its
allowed grafting-depth summands are the displayed eigenspaces, and the depth
labels are distinct on the allowed range. -/
def claim19636 : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    diagonalizableEndomorphism
      (glOperator n (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_two hn))) ∧
      ∀ (k : ℕ), allowedDepth n k →
        ∃ hDepth : k ≤ n,
          tower n k hDepth =
            Module.End.eigenspace
              (glOperator n
                (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_two hn)))
              (depthEigenvalue n k) ∧
          ∀ (j : ℕ), allowedDepth n j → k ≠ j →
            depthEigenvalue n k ≠ depthEigenvalue n j

/-- One factor in the finite Lagrange product. -/
def depthProjectorFactor (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Module.End ℚ (TreeSpace n) :=
  (-depthEigenvalue n k)⁻¹ •
    (glOperator n hn -
      depthEigenvalue n k • (LinearMap.id : Module.End ℚ (TreeSpace n)))

/-- The finite product of the nonzero, non-exceptional depth factors. -/
def depthProjector (n : ℕ) (hn : 0 < n) :
    Module.End ℚ (TreeSpace n) :=
  List.foldl (fun P k => P.comp (depthProjectorFactor n hn k))
    (LinearMap.id : Module.End ℚ (TreeSpace n)) (List.range' 1 (n - 2))

/-- Claim 19637: the Lagrange polynomial in `GL` is an idempotent whose image
is exactly the degree-`n` leaf kernel and which fixes that kernel pointwise. -/
def claim19637 : Prop :=
  ∀ (n : ℕ) (hTop : 2 ≤ n),
    let hn : 0 < n := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_two hTop)
    let projector := depthProjector n hn
    projector.comp projector = projector ∧
      LinearMap.range projector = LinearMap.ker (leafDeletion n) ∧
      ∀ v : TreeSpace n, v ∈ LinearMap.ker (leafDeletion n) → projector v = v

end

end MathlibPlus.Open.ResearchFormalization.R0310LeafSpectrumClaims
