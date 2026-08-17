import MathlibPlus.Open.UnnormalizedQuantizedRelation

namespace MathlibPlus.Open.ResearchFormalizationD0075

open MathlibPlus.Open.UnnormalizedQuantizedRelation

noncomputable section

/-- The normalized `A L` endomorphism on the degree-`n` graph space. -/
def deckDepthOperator (n : ℕ) :
    FiniteSimpleGraph.Space n →ₗ[ℚ] FiniteSimpleGraph.Space n :=
  normalizedUpperPrevious n ∘ₗ lower n

/-- Iterated normalized lifting, before transporting its target along a
natural-number equality. -/
def normalizedLiftPower : (m k : ℕ) →
    FiniteSimpleGraph.Space m →ₗ[ℚ]
      FiniteSimpleGraph.Space (m + k)
  | m, 0 => LinearMap.id
  | m, k + 1 =>
      (normalizedLift (m + k)).comp (normalizedLiftPower m k)

/-- Transport a graph space along an equality of its degree indices. -/
def transportSpace {a b : ℕ} (h : a = b) :
    FiniteSimpleGraph.Space a →ₗ[ℚ] FiniteSimpleGraph.Space b :=
  h ▸ LinearMap.id

/-- Iterated `A` from degree `n-k` to degree `n`. -/
def normalizedLiftPowerTo (n k : ℕ) (h : k ≤ n) :
    FiniteSimpleGraph.Space (n - k) →ₗ[ℚ] FiniteSimpleGraph.Space n :=
  (transportSpace (Nat.sub_add_cancel h)).comp
    (normalizedLiftPower (n - k) k)

/-- The actual `A^k(ker L_(n-k))` submodule at degree `n`. -/
def deckDepthImage (n k : ℕ) :
    Submodule ℚ (FiniteSimpleGraph.Space n) :=
  if h : k ≤ n then
    Submodule.map (normalizedLiftPowerTo n k h)
      (LinearMap.ker (lower (n - k)))
  else ⊥

/-- The eigenvalues of the concrete degree-`n` deck-depth operator. -/
def deckDepthEigenvalueSet (n : ℕ) : Set ℚ :=
  {value : ℚ |
    ∃ (x : FiniteSimpleGraph.Space n),
      x ≠ 0 ∧ deckDepthOperator n x = value • x}

/-- Diagonalizability by an eigenbasis of the concrete degree-`n` space. -/
def deckDepthDiagonalizable (n : ℕ) : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι ℚ (FiniteSimpleGraph.Space n))
    (eigenvalue : ι → ℚ),
    ∀ i, deckDepthOperator n (b i) = eigenvalue i • b i

/-- The integer spectrum and all depth eigenspaces of the concrete deck-depth
operator, including the degree-preserving type of `A L` and the depth-zero
identification with the deck kernel. -/
def deckDepthSpectralDecomposition_claim5009 : Prop :=
  ∀ n : ℕ,
    deckDepthDiagonalizable n ∧
      deckDepthEigenvalueSet n =
        ({value : ℚ |
          ∃ (k : ℕ), k + 2 ≤ n ∧ value = (k : ℚ)} ∪
          Set.singleton (n : ℚ)) ∧
      (∀ k : ℕ, k + 2 ≤ n ∨ k = n →
        Module.End.eigenspace (deckDepthOperator n) (k : ℚ) =
          deckDepthImage n k) ∧
      Module.End.eigenspace (deckDepthOperator n) 0 =
        LinearMap.ker (lower n)

end

end MathlibPlus.Open.ResearchFormalizationD0075
