import Mathlib
import MathlibPlus.Open.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Open.FormalizationBatch

/-- The action of a vertex permutation on a rational coordinate vector. -/
def permuteCoordinateVector {n : ℕ} (σ : Equiv.Perm (Fin n))
    (d : Fin n → ℚ) : Fin n → ℚ :=
  fun u => d (σ u)

/-- The affine-reflection branch at the coordinate fixed by a card. -/
def affineReflectionVector {n : ℕ} (i : Fin n) (d : Fin n → ℚ) : Fin n → ℚ :=
  fun u => 2 * d i - d u

/-- The exact two-branch action context on the common two-dimensional kernel. -/
def twoDimensionalCardActionContext {n : ℕ}
    (π : PointedLocalPermutations (Fin n))
    (d : Fin n → ℚ)
    (K : Submodule ℚ (Fin n → ℚ)) : Prop :=
  K = Submodule.span ℚ ({(fun _ => (1 : ℚ)), d} : Set (Fin n → ℚ)) ∧
    (∀ i : Fin n,
      ((permuteCoordinateVector (π.1 i) d = d) ∨
        (permuteCoordinateVector (π.1 i) d = affineReflectionVector i d)) ∧
      ¬(permuteCoordinateVector (π.1 i) d = d ∧
        permuteCoordinateVector (π.1 i) d = affineReflectionVector i d)) ∧
    (∀ i : Fin n, ∀ x : Fin n → ℚ, x ∈ K →
      permuteCoordinateVector (π.1 i) x ∈ K)

/-- Claim 17086: a nonconstant finite degree vector cannot have every card in
its affine-reflection branch; one card fixes the vector and the full kernel. -/
def claim17086_notEveryCardAffineReflection : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (π : PointedLocalPermutations (Fin n)) (d : Fin n → ℚ)
      (K : Submodule ℚ (Fin n → ℚ)),
      (∃ u v : Fin n, d u ≠ d v) →
      (∀ i : Fin n, Function.Involutive (π.1 i)) →
      twoDimensionalCardActionContext π d K →
      (¬ (∀ i : Fin n,
        permuteCoordinateVector (π.1 i) d = affineReflectionVector i d)) ∧
      ∃ i : Fin n,
        permuteCoordinateVector (π.1 i) d = d ∧
          ∀ x : Fin n → ℚ, x ∈ K →
            permuteCoordinateVector (π.1 i) x = x

end MathlibPlus.Open.ResearchFormalization
