import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalize

/-- The ordered Cayley section matrix attached to a finite subset. -/
def cayleySectionMatrix {A : Type*} [Fintype A] [DecidableEq A]
    [AddCommGroup A] (U : Finset A) : Matrix A A ℂ :=
  fun x y => if y - x ∈ U then 1 else 0

/-- Matrix multiplication written explicitly so the ordered intermediate label is visible. -/
def sectionMatrixMul {A : Type*} [Fintype A]
    (M N : Matrix A A ℂ) : Matrix A A ℂ :=
  fun x z => ∑ y : A, M x y * N y z

/-- Transpose for the section matrices. -/
def sectionMatrixTranspose {A : Type*}
    (M : Matrix A A ℂ) : Matrix A A ℂ :=
  fun x y => M y x

/-- Entrywise (Hadamard) product for the section matrices. -/
def sectionMatrixHadamard {A : Type*}
    (M N : Matrix A A ℂ) : Matrix A A ℂ :=
  fun x y => M x y * N x y

/-- Matrix action on a column vector, with the finite sum exposed. -/
def sectionMatrixVecMul {A : Type*} [Fintype A]
    (M : Matrix A A ℂ) (v : A → ℂ) : A → ℂ :=
  fun x => ∑ y : A, M x y * v y

/-- The section labelled by the negatives of a finite subset. -/
def negSectionSet {A : Type*} [DecidableEq A]
    [AddGroup A] (U : Finset A) : Finset A :=
  U.image Neg.neg

/-- A nonzero complex-valued character of a finite additive group. -/
def IsComplexCharacter {A : Type*} [AddZeroClass A]
    (χ : A → ℂ) : Prop :=
  (χ 0 = 1) ∧ (∀ x, χ x ≠ 0) ∧ (∀ x y, χ (x + y) = χ x * χ y)

/--
The convolution, transpose, Hadamard, and character-eigenvector identities,
including the ordered section labels in the double sum.
-/
def convolutionTransposeHadamardClaim : Prop := by
  classical
  exact ∀ {A : Type*} [Fintype A] [DecidableEq A] [AddCommGroup A]
      (U V : Finset A),
    sectionMatrixMul (cayleySectionMatrix U) (cayleySectionMatrix V) =
        (∑ u ∈ U, ∑ v ∈ V, cayleySectionMatrix ({u + v} : Finset A)) ∧
      sectionMatrixTranspose (cayleySectionMatrix U) =
        cayleySectionMatrix (negSectionSet U) ∧
      sectionMatrixHadamard (cayleySectionMatrix U) (cayleySectionMatrix V) =
        cayleySectionMatrix (U ∩ V) ∧
      ∀ (χ : A → ℂ), IsComplexCharacter χ → ∀ x : A,
        sectionMatrixVecMul (cayleySectionMatrix U) χ x =
          (∑ u ∈ U, χ u) * χ x

end MathlibPlus.Open.ResearchFormalize
