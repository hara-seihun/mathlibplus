import Mathlib

noncomputable section

namespace MathlibPlus.Open.NewResearch2.Jacobsthal

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The covering function uses one residue class for every prime up to the cutoff. -/
def claim_16711 : Prop :=
  let primes := fun X : ℕ =>
    (Finset.range (X + 1)).filter Nat.Prime
  let covers := fun (X Y : ℕ) (a : ℕ → ℕ) =>
    ∀ n : Fin Y, ∃ p ∈ primes X,
      (n.val + 1) % p = a p % p
  ∀ X : ℕ, ∃ Y : ℕ,
    (∃ a : ℕ → ℕ, covers X Y a) ∧
    (∀ a : ℕ → ℕ, ¬ covers X (Y + 1) a) ∧
    (∀ Z : ℕ, (∃ a : ℕ → ℕ, covers X Z a) → Z ≤ Y)

/-- The primorial identity is the exact least-interval formulation of Jacobsthal's function. -/
def claim_16712 : Prop :=
  let primes := fun X : ℕ => (Finset.range (X + 1)).filter Nat.Prime
  let primorial := fun X : ℕ => Finset.prod (primes X) (fun p => p)
  let covers := fun (X Y : ℕ) (a : ℕ → ℕ) =>
    ∀ n : Fin Y, ∃ p ∈ primes X,
      (n.val + 1) % p = a p % p
  let largest := fun X Y : ℕ =>
    (∃ a : ℕ → ℕ, covers X Y a) ∧
      (∀ a : ℕ → ℕ, ¬ covers X (Y + 1) a) ∧
      (∀ Z : ℕ, (∃ a : ℕ → ℕ, covers X Z a) → Z ≤ Y)
  let jacobsthal := fun n j : ℕ =>
    0 < j ∧
      (∀ a : ℕ, ∃ t : Fin j, Nat.Coprime (a + t.val) n) ∧
      (∀ k : ℕ, k < j → ¬ ∀ a : ℕ,
        ∃ t : Fin k, Nat.Coprime (a + t.val) n)
  ∀ X : ℕ, ∃ Y j : ℕ,
    largest X Y ∧ jacobsthal (primorial X) j ∧ Y + 1 = j

/-- The known quadratic upper bound, stated with the exact maximal covering function. -/
def claim_16713 : Prop :=
  let primes := fun X : ℕ => (Finset.range (X + 1)).filter Nat.Prime
  let covers := fun (X Y : ℕ) (a : ℕ → ℕ) =>
    ∀ n : Fin Y, ∃ p ∈ primes X,
      (n.val + 1) % p = a p % p
  let largest := fun X Y : ℕ =>
    (∃ a : ℕ → ℕ, covers X Y a) ∧
      (∀ a : ℕ → ℕ, ¬ covers X (Y + 1) a) ∧
      (∀ Z : ℕ, (∃ a : ℕ → ℕ, covers X Z a) → Z ≤ Y)
  ∃ Y : ℕ → ℕ, ∃ C X₀ : ℕ,
    0 < C ∧
    (∀ X : ℕ, largest X (Y X)) ∧
    (∀ X : ℕ, X₀ ≤ X → Y X ≤ C * X ^ 2)

/-- The known lower bound with the packet's triple-logarithmic factor. -/
def claim_16714 : Prop :=
  let primes := fun X : ℕ => (Finset.range (X + 1)).filter Nat.Prime
  let covers := fun (X Y : ℕ) (a : ℕ → ℕ) =>
    ∀ n : Fin Y, ∃ p ∈ primes X,
      (n.val + 1) % p = a p % p
  let largest := fun X Y : ℕ =>
    (∃ a : ℕ → ℕ, covers X Y a) ∧
      (∀ a : ℕ → ℕ, ¬ covers X (Y + 1) a) ∧
      (∀ Z : ℕ, (∃ a : ℕ → ℕ, covers X Z a) → Z ≤ Y)
  ∃ Y : ℕ → ℕ, ∃ c X₀ : ℕ,
    0 < c ∧
    (∀ X : ℕ, largest X (Y X)) ∧
    (∀ X : ℕ, X₀ ≤ X →
      (Y X : ℝ) ≥ (c : ℝ) * X * Real.log X *
        Real.log (Real.log (Real.log X)) / Real.log (Real.log X))

/-- The inverse cutoff formulation of subquadratic growth. -/
def claim_16718 : Prop :=
  let primes := fun X : ℕ => (Finset.range (X + 1)).filter Nat.Prime
  let covers := fun (X Y : ℕ) (a : ℕ → ℕ) =>
    ∀ n : Fin Y, ∃ p ∈ primes X,
      (n.val + 1) % p = a p % p
  let coverAt := fun X Y : ℕ => ∃ a : ℕ → ℕ, covers X Y a
  let largest := fun X Y : ℕ =>
    coverAt X Y ∧
      (∀ a : ℕ → ℕ, ¬ covers X (Y + 1) a) ∧
      (∀ Z : ℕ, coverAt X Z → Z ≤ Y)
  ∃ Y f : ℕ → ℕ,
    (∀ X : ℕ, largest X (Y X)) ∧
    (∀ Z : ℕ, coverAt (f Z) Z ∧
      (∀ X : ℕ, X < f Z → ¬ coverAt X Z)) ∧
    ((∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        (Y X : ℝ) ≤ ε * X ^ 2) ↔
      (∀ M : ℝ, 0 < M → ∃ Z₀ : ℕ, ∀ Z : ℕ, Z₀ ≤ Z →
        (f Z : ℝ) / Real.sqrt Z > M))

end MathlibPlus.Open.NewResearch2.Jacobsthal
