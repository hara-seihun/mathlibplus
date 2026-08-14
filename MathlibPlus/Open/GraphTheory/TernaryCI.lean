import Mathlib

namespace MathlibPlus.Open.GraphTheory.TernaryCI

noncomputable section

private abbrev TernaryPower (r : ℕ) := Fin r → Multiplicative (ZMod 3)

private def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ x⁻¹ ∈ S

private def undirectedCI (G : Type*) [Group G] : Prop :=
  ∀ S T : Set G,
    inverseClosed S → inverseClosed T → 1 ∉ S → 1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ φ : G ≃* G, φ '' S = T

/-- Claim 28361: the rank-eight ternary elementary abelian group has an
explicit inverse-closed Cayley graph defect. -/
def claim28361_rankEightTernaryNonCI : Prop :=
  ∃ S T : Set (TernaryPower 8),
    inverseClosed S ∧ inverseClosed T ∧ 1 ∉ S ∧ 1 ∉ T ∧
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) ∧
        ∀ φ : TernaryPower 8 ≃* TernaryPower 8, φ '' S ≠ T

/-- Claim 28362: every finite group containing a rank-eight ternary subgroup
fails the undirected graph-CI property. -/
def claim28362_finiteOvergroupNonCI : Prop :=
  ∀ (G : Type*) [Finite G] [Group G],
    (∃ H : Subgroup G, Nonempty (TernaryPower 8 ≃* H)) →
      ¬ undirectedCI G

/-- Claim 28363: every ternary elementary abelian group of rank at least eight
fails the undirected graph-CI property. -/
def claim28363_allHigherTernaryRanksNonCI : Prop :=
  ∀ r : ℕ, 8 ≤ r → ¬ undirectedCI (TernaryPower r)

end

end MathlibPlus.Open.GraphTheory.TernaryCI
