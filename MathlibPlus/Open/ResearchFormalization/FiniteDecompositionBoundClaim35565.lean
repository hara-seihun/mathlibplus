import MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

namespace MathlibPlus.Open.ResearchFormalization.FiniteDecompositionBoundClaim35565

open Classical
open BigOperators
open MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

noncomputable section

abbrev F2 := ZMod 2
abbrev F2Cube (n : ℕ) := Fin n → F2
abbrev EdgeSystem (n : ℕ) :=
  ∀ i : Fin n, F2Omega n i → Bool
abbrev CharacterSpace (n : ℕ) :=
  F2Cube n →ₗ[F2] F2

/-- The actual coordinate character on `𝔽₂ⁿ`. -/
def coordinateCharacter {n : ℕ} (i : Fin n) : CharacterSpace n :=
  LinearMap.proj i

/-- Pullback of the full dual of an exact quotient map. -/
def pullbackCharacterSpace {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module F2 W]
    (F : F2Cube n →ₗ[F2] W) : Submodule F2 (CharacterSpace n) :=
  LinearMap.range (LinearMap.dualMap F)

def quotientCharacterSpace {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module F2 W]
    (i : Fin n) (F : F2Cube n →ₗ[F2] W) :
    Submodule F2 (CharacterSpace n) :=
  pullbackCharacterSpace F ⊔
    Submodule.span F2 {coordinateCharacter i}

def blockExcess (r : ℕ) : ℝ :=
  (2 : ℝ) ^ r + ((r + 1 : ℕ) : ℝ) / 2

def sunflowerRemainder (r t : ℕ) (C : ℝ) : ℝ :=
  ((r + 1 : ℕ) : ℝ) * ((t - 1 : ℕ) : ℝ) *
    (C * (t : ℝ) *
      Real.log (2 * ((2 ^ (r + 1) - 1 : ℕ) : ℝ))) ^
        (2 ^ (r + 1) - 1)

/-- Exact coordinate quotient data for the literal edge functions.  The
maps are genuine linear quotients on `𝔽₂ⁿ`, the selected sets live in their
actual quotient carriers, and the direct-sum character spaces are retained. -/
def exactQuotientPresentation {n : ℕ} (r : ℕ)
    (f : EdgeSystem n) (W : Fin n → Type*)
    [∀ i : Fin n, Fintype (W i)]
    [∀ i : Fin n, AddCommGroup (W i)]
    [∀ i : Fin n, Module F2 (W i)]
    (F : ∀ i : Fin n, F2Cube n →ₗ[F2] W i)
    (S : ∀ i : Fin n, Finset (W i)) : Prop :=
  (∀ i : Fin n, Module.finrank F2 (W i) ≤ r) ∧
    (∀ i : Fin n, Function.Surjective (F i)) ∧
    (∀ i : Fin n, ∀ a : F2,
      F i (Pi.single i a) = 0) ∧
    (∀ i : Fin n,
      pullbackCharacterSpace (F i) ⊓
          Submodule.span F2 {coordinateCharacter i} = ⊥) ∧
    (∀ i : Fin n, ∀ x : F2Omega n i,
      f i x = decide (F i x.1 ∈ S i))

/-- A common-center block is defined using the actual pullback character
spaces of its quotient maps, with no free rank labels or abstract blocks. -/
def commonCenterBlock {n r : ℕ}
    (W : Fin n → Type*)
    [∀ i : Fin n, Fintype (W i)]
    [∀ i : Fin n, AddCommGroup (W i)]
    [∀ i : Fin n, Module F2 (W i)]
    (F : ∀ i : Fin n, F2Cube n →ₗ[F2] W i)
    (I : Finset (Fin n))
    (C : Submodule F2 (CharacterSpace n)) : Prop :=
  (∃ d : ℕ, d ≤ r ∧ ∀ i ∈ I,
      Module.finrank F2 (W i) = d) ∧
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      quotientCharacterSpace i (F i) ⊓ quotientCharacterSpace j (F j) = C)

def finiteDecompositionWitness {n r t : ℕ} (C₀ : ℝ)
    (f : EdgeSystem n) (W : Fin n → Type*)
    [∀ i : Fin n, Fintype (W i)]
    [∀ i : Fin n, AddCommGroup (W i)]
    [∀ i : Fin n, Module F2 (W i)]
    (F : ∀ i : Fin n, F2Cube n →ₗ[F2] W i)
    (Iset : Finset (Finset (Fin n)))
    (remainder : Finset (Fin n)) : Prop :=
  (∀ i : Fin n,
    i ∈ remainder ↔
      ¬ ∃ I : Finset (Fin n), I ∈ Iset ∧ i ∈ I) ∧
    (∀ I ∈ Iset, t ≤ I.card) ∧
    (∀ I ∈ Iset, ∀ J ∈ Iset, I ≠ J → Disjoint I J) ∧
    (∀ I ∈ Iset, ∃ C : Submodule F2 (CharacterSpace n),
      commonCenterBlock (r := r) W F I C) ∧
    (∀ I ∈ Iset,
      (∑ i ∈ I, f2Density f i) ≤
        (I.card : ℝ) / 2 + blockExcess r) ∧
    (remainder.card : ℝ) < sunflowerRemainder r t C₀

/-- Claim 35565: exact quotient maps and exact common-center blocks are
extracted separately within each rank class; their block excess and literal remainder
combine to the displayed bound. -/
def finiteDecompositionBound_claim35565 : Prop :=
  ∀ (n r t : ℕ) (C₀ : ℝ) (f : EdgeSystem n)
    (W : Fin n → Type*)
    [∀ i : Fin n, Fintype (W i)]
    [∀ i : Fin n, AddCommGroup (W i)]
    [∀ i : Fin n, Module F2 (W i)]
    (F : ∀ i : Fin n, F2Cube n →ₗ[F2] W i)
    (S : ∀ i : Fin n, Finset (W i)),
    4 ≤ C₀ → 2 ≤ t → f2C4Free f →
      exactQuotientPresentation r f W F S →
        ∃ Iset : Finset (Finset (Fin n)),
          ∃ remainder : Finset (Fin n),
            finiteDecompositionWitness (r := r) (t := t)
              C₀ f W F Iset remainder ∧
              (∑ i : Fin n, f2Density f i) ≤
                (n : ℝ) / 2 + (n : ℝ) * blockExcess r / (t : ℝ) +
                  sunflowerRemainder r t C₀ / 2

end
end MathlibPlus.Open.ResearchFormalization.FiniteDecompositionBoundClaim35565
