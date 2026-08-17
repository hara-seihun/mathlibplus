import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.NewResearch2.R0582

noncomputable section

/-- The polynomial carrier with zero-based indices for the labels
`c₁,c₂,…` and `o₁,o₂,…`. -/
abbrev ComponentPolynomial := MvPolynomial (ℕ ⊕ ℕ) ℚ

def closedLabel (k : ℕ) : ComponentPolynomial :=
  MvPolynomial.X (Sum.inl k)

def openLabel (k : ℕ) : ComponentPolynomial :=
  MvPolynomial.X (Sum.inr k)

/-- The source component-size grading, with `k=0` representing subscript one. -/
def componentDegree : (ℕ ⊕ ℕ) → ℕ
  | Sum.inl k => k + 1
  | Sum.inr k => k + 1

def monomialComponentDegree
    (m : (ℕ ⊕ ℕ) →₀ ℕ) : ℕ :=
  m.sum (fun label exponent => exponent * componentDegree label)

def homogeneousComponentDegree
    (p : ComponentPolynomial) (n : ℕ) : Prop :=
  ∀ a ∈ p.support, monomialComponentDegree a = n

def primitiveTensor (x : ComponentPolynomial) :
    ComponentPolynomial ⊗[ℚ] ComponentPolynomial :=
  x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] x

/-- Exact unital, additive, multiplicative coproduct semantics with every
component label primitive. -/
def primitiveCoproduct
    (D : ComponentPolynomial →
      ComponentPolynomial ⊗[ℚ] ComponentPolynomial) : Prop :=
  D 1 = (1 : ComponentPolynomial) ⊗ₜ[ℚ] 1 ∧
    (∀ p q, D (p + q) = D p + D q) ∧
    (∀ p q, D (p * q) = D p * D q) ∧
    (∀ k, D (closedLabel k) = primitiveTensor (closedLabel k)) ∧
    (∀ k, D (openLabel k) = primitiveTensor (openLabel k))

def rootedSingleton : ComponentPolynomial :=
  closedLabel 0 + openLabel 0

def rootedEdge : ComponentPolynomial :=
  closedLabel 0 ^ 2 + closedLabel 1 +
    openLabel 0 * closedLabel 0 + openLabel 1

/-- Claim 22967: with the exact component-size grading and primitive
coproduct, the rooted-edge factor splits into the two unmixed terms and the
mixed rooted-singleton/`x₁` terms. -/
def exact_induced_split_rooted_edge_claim22967 : Prop :=
  ∀ D : ComponentPolynomial →
      ComponentPolynomial ⊗[ℚ] ComponentPolynomial,
    primitiveCoproduct D →
      D rootedEdge =
        rootedEdge ⊗ₜ[ℚ] (1 : ComponentPolynomial) +
          (1 : ComponentPolynomial) ⊗ₜ[ℚ] rootedEdge +
          rootedSingleton ⊗ₜ[ℚ] closedLabel 0 +
          closedLabel 0 ⊗ₜ[ℚ] rootedSingleton

end

end MathlibPlus.Open.NewResearch2.R0582
