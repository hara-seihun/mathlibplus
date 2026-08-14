import Mathlib

namespace MathlibPlus.Open.GroupTheory.PermutationEGroupBatch

def IsRegularPermutationSubgroup {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : H, g.1 x = y

def HasERegularCopy {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (m : ℕ) (G : Subgroup (Equiv.Perm Ω)) (a b : Equiv.Perm Ω) : Prop :=
  a ∈ G ∧ b ∈ G ∧
    a ^ m = 1 ∧
    (∀ k : ℕ, 0 < k → k < m → a ^ k ≠ 1) ∧
    b ^ 8 = 1 ∧
    (∀ k : ℕ, 0 < k → k < 8 → b ^ k ≠ 1) ∧
    b⁻¹ * a * b = a⁻¹ ∧
    Set.ncard (Subgroup.closure ({a, b} : Set (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) = 8 * m ∧
    IsRegularPermutationSubgroup
      (Subgroup.closure ({a, b} : Set (Equiv.Perm Ω)))

def IsPrimitivePermutationGroup {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ x y : Ω, ∃ g : G, g.1 x = y) ∧
    (∀ B : Set Ω,
      B.Nonempty →
      (∀ g : G,
        g.1 '' B = B ∨ Disjoint (g.1 '' B) B) →
      B.Subsingleton ∨ B = Set.univ)

def IsTwoTransitivePermutationGroup {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : Ω,
    x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : G, g.1 x₁ = y₁ ∧ g.1 x₂ = y₂

/-- The primitive-group conclusion for a regular copy of the displayed
presentation `a^m=b^8=1`, `b⁻¹ab=a⁻¹`. -/
def OddEighthExtensionPrimitiveConclusion : Prop :=
  ∀ (m : ℕ), 1 < m → m % 2 = 1 →
    ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω]
      (G : Subgroup (Equiv.Perm Ω)),
      IsPrimitivePermutationGroup G →
      (∃ a b : Equiv.Perm Ω, HasERegularCopy m G a b) →
      IsTwoTransitivePermutationGroup G

end MathlibPlus.Open.GroupTheory.PermutationEGroupBatch
