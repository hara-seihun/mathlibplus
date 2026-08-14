import Mathlib

namespace MathlibPlus.Open.NewResearch2.CI

private def cyclicFinite (G : Type*) [AddCommGroup G] [Fintype G] : Prop :=
  ∃ g : G, ∀ x : G, ∃ k : ℤ, k • g = x

private def cayleyAdj (n : ℕ) (S : Set (ZMod n)) (x y : ZMod n) : Prop :=
  x ≠ y ∧ y - x ∈ S

private def undirectedCIGroup (n : ℕ) : Prop :=
  ∀ (S T : Set (ZMod n)),
    0 ∉ S → 0 ∉ T →
    (∀ x : ZMod n, -x ∈ S ↔ x ∈ S) →
    (∀ x : ZMod n, -x ∈ T ↔ x ∈ T) →
    ∀ e : ZMod n ≃ ZMod n,
      (∀ x y, cayleyAdj n S x y ↔ cayleyAdj n T (e x) (e y)) →
      ∃ φ : ZMod n ≃+ ZMod n,
        ∀ x y, y - x ∈ S ↔ φ y - φ x ∈ T

/-- Claim 14523: cell A1 is the positive-integer cyclic parameterization. -/
def claim14523 : Prop :=
  (∀ (G : Type*) [AddCommGroup G] [Fintype G],
    cyclicFinite G ↔
      ∃ n : ℕ, 0 < n ∧ Nonempty (G ≃+ ZMod n)) ∧
  (∀ n : ℕ, 0 < n →
    ∃ g : ZMod n, ∀ x : ZMod n, ∃ k : ℤ, k • g = x)

/-- Claim 14524: the listed positive cyclic parameters are undirected
CI-groups. -/
def claim14524 : Prop :=
  ∀ n : ℕ,
    (n = 8 ∨ n = 9 ∨ n = 18 ∨
      ∃ m k : ℕ, (m = 1 ∨ m = 2 ∨ m = 4) ∧ n = m * k ∧
        0 < k ∧ (∀ p : ℕ, p.Prime → p ∣ k → ¬p ^ 2 ∣ k) ∧ k % 2 = 1) →
    undirectedCIGroup n

/-- Claim 14526: complete finite undirected cyclic CI classification. -/
def claim14526 : Prop :=
  ∀ n : ℕ, 0 < n →
    undirectedCIGroup n ↔
      (n = 8 ∨ n = 9 ∨ n = 18 ∨
        ∃ m k : ℕ, (m = 1 ∨ m = 2 ∨ m = 4) ∧ n = m * k ∧
          0 < k ∧ (∀ p : ℕ, p.Prime → p ∣ k → ¬p ^ 2 ∣ k) ∧ k % 2 = 1)

end MathlibPlus.Open.NewResearch2.CI
