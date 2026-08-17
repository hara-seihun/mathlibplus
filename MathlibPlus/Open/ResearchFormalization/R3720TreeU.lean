import Mathlib
import MathlibPlus.Open.TreeSpectral
import MathlibPlus.Open.Research.TreeCuts

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3720

noncomputable section

open MathlibPlus.Open.TreeSpectral
open MathlibPlus.Open.Research.TreeCuts

abbrev ResearchVariable := ℕ+
abbrev ResearchPolynomial := MvPolynomial ResearchVariable ℚ

/-- The positive-index variable corresponding to a component of size `k`.
The zero branch is irrelevant for genuine connected components, whose size is
positive. -/
def positiveVariable (k : ℕ) : ResearchVariable :=
  if h : 0 < k then ⟨k, h⟩ else ⟨1, by omega⟩

/-- The component-size monomial in the positive-index polynomial carrier. -/
noncomputable def positiveComponentMonomial {V : Type} [Fintype V]
    (p : Setoid V) : ResearchPolynomial :=
  MvPolynomial.rename positiveVariable
    (MvPolynomial.map (Int.castRingHom ℚ) (componentMonomial p))

/-- The ordinary edge-subset/component-size U-polynomial over `ℚ`. -/
noncomputable def positiveStanleyU {V : Type} [Fintype V]
    (T : SimpleGraph V) : ResearchPolynomial :=
  MvPolynomial.rename positiveVariable
    (MvPolynomial.map (Int.castRingHom ℚ) (stanleyU T))

/-- The U-polynomial of an unlabelled tree, using the canonical quotient
representative supplied by the tree carrier. -/
noncomputable def treeUPolynomial {n : ℕ} (T : TreeClass n) : ResearchPolynomial :=
  positiveStanleyU (Quotient.out T).1

/-- The linear U-map on the rational span of unlabelled tree types. -/
noncomputable def uMap (n : ℕ) :
    TreeSpace n →ₗ[ℚ] ResearchPolynomial :=
  Finsupp.linearCombination ℚ (fun T => treeUPolynomial T)

/-- Leaf deletion followed by transport from `(n+1)-1` to `n`. -/
noncomputable def leafDeletionSucc (n : ℕ) :
    TreeSpace (n + 1) →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace (Nat.add_sub_cancel n 1)).comp
    (leafDeletion (n + 1))

/-- Grafting from the predecessor degree, transported to degree `n`. -/
noncomputable def graftPred (n : ℕ) (h : 1 ≤ n) :
    TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace (Nat.sub_add_cancel h)).comp
    (graft (n - 1))

/-- The first leaf-deletion moment map `M_n = U_(n-1) ∘ L_n`. -/
noncomputable def momentMap (n : ℕ) :
    TreeSpace n →ₗ[ℚ] ResearchPolynomial :=
  (uMap (n - 1)).comp (leafDeletion n)

def firstVariable : ResearchVariable :=
  ⟨1, by decide⟩

def successorVariable (a : ResearchVariable) : ResearchVariable :=
  ⟨a.1 + 1, Nat.succ_pos _⟩

def weightHomogeneous (n : ℕ) (f : ResearchPolynomial) : Prop :=
  MvPolynomial.IsWeightedHomogeneous (fun a : ResearchVariable => a.1) f n

/-- The finite polynomial realization of the derivation
`Σ_{a≥1} a x_(a+1) ∂_(x_a)`. -/
noncomputable def researchDelta (f : ResearchPolynomial) : ResearchPolynomial :=
  ∑ a ∈ f.vars,
    MvPolynomial.C (a.1 : ℚ) * MvPolynomial.X (successorVariable a) *
      (MvPolynomial.pderiv a) f

/-- The polynomial raising operator `Γ_n = n x₁ + δ`. -/
noncomputable def researchGamma (n : ℕ) (f : ResearchPolynomial) : ResearchPolynomial :=
  MvPolynomial.C (n : ℚ) * MvPolynomial.X firstVariable * f +
    researchDelta f

/-- Injectivity of `Γ_n` on its homogeneous weight-`n` component. -/
def gammaWeightInjective (n : ℕ) : Prop :=
  ∀ f g : ResearchPolynomial,
    weightHomogeneous n f → weightHomogeneous n g →
      researchGamma n f = researchGamma n g → f = g

/-- The kernel of the U-map. -/
def uKernel (n : ℕ) : Submodule ℚ (TreeSpace n) :=
  LinearMap.ker (uMap n)

/-- The joint U/first-moment kernel. -/
def jointKernel (n : ℕ) : Submodule ℚ (TreeSpace n) :=
  uKernel n ⊓ LinearMap.ker (momentMap n)

/-- The joint kernel viewed as a submodule of the U-kernel. -/
def jointKernelInKernel (n : ℕ) : Submodule ℚ (uKernel n) :=
  (jointKernel n).comap (uKernel n).subtype

abbrev kernelQuotient (n : ℕ) :=
  uKernel n ⧸ jointKernelInKernel n

/-- Claim 48412: the all-vertex grafting map intertwines with the polynomial
raising operator on the exact tree and polynomial carriers. -/
def claim_48412 : Prop :=
  ∀ n : ℕ,
    (∀ w : TreeSpace n, weightHomogeneous n (uMap n w)) ∧
    (∀ f : ResearchPolynomial, weightHomogeneous n f →
      weightHomogeneous (n + 1) (researchGamma n f)) ∧
    (∀ w : TreeSpace n,
      uMap (n + 1) (graft n w) = researchGamma n (uMap n w))

/-- Claim 48413: leaf deletion and all-vertex grafting obey the up-down
relation, with occurrence multiplicity retained. -/
def claim_48413 : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    let h : 1 ≤ n := le_trans (by decide) hn
    (leafDeletionSucc n).comp (graft n) -
        (graftPred n h).comp (leafDeletion n) =
      (n : ℚ) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)

/-- Claim 48414: the up-down relation transports the first pendant moment and
has the stated specialization on the U-kernel. -/
def claim_48414 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ w : TreeSpace n,
      momentMap (n + 1) (graft n w) =
        researchGamma (n - 1) (momentMap n w) + (n : ℚ) • uMap n w) ∧
    (∀ w : TreeSpace n, uMap n w = 0 →
      momentMap (n + 1) (graft n w) =
        researchGamma (n - 1) (momentMap n w))

/-- Claim 48416: the U-kernel and joint kernel are transported by grafting,
and grafting gives an injective map on their quotient spaces. -/
def claim_48416 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    gammaWeightInjective (n - 1) ∧
    (∀ w : TreeSpace n, w ∈ uKernel n →
      graft n w ∈ uKernel (n + 1)) ∧
    (∀ w : TreeSpace n, w ∈ jointKernel n →
      graft n w ∈ jointKernel (n + 1)) ∧
    (∀ w : TreeSpace n, w ∈ uKernel n →
      graft n w ∈ jointKernel (n + 1) → w ∈ jointKernel n) ∧
    (∃ gK : uKernel n →ₗ[ℚ] uKernel (n + 1),
      (∀ w : uKernel n,
        (gK w : TreeSpace (n + 1)) = graft n (w : TreeSpace n)) ∧
      (∀ z : jointKernelInKernel n,
        gK z ∈ jointKernelInKernel (n + 1)) ∧
      ∃ φ : kernelQuotient n →ₗ[ℚ] kernelQuotient (n + 1),
        Function.Injective φ ∧
        (∀ w : uKernel n,
          φ ((jointKernelInKernel n).mkQ w) =
            (jointKernelInKernel (n + 1)).mkQ (gK w)))

end
end MathlibPlus.Open.ResearchFormalization.R3720
