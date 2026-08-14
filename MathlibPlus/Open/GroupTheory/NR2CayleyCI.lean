import Mathlib

namespace MathlibPlus.Open.GroupTheory.NR2FormalizationDrain

noncomputable section

/-- The ordinary undirected Cayley CI property is the exact graph-CI carrier
used by the project's Cayley hierarchy. -/
def cayleyGraphCI (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
      ∃ φ : G ≃* G, φ '' S = T
def undirectedCIGroup (G : Type*) [Group G] [Finite G] : Prop := cayleyGraphCI G
abbrev elementaryAbelian (p r : ℕ) := Multiplicative (Fin r → ZMod p)
def claim28356 : Prop := ∀ p : ℕ, ∀ hp : Nat.Prime p, 3 < p →
  letI : NeZero p := ⟨hp.ne_zero⟩
  ¬ undirectedCIGroup (elementaryAbelian p (2 * p + 3))
def claim28357 : Prop := ∀ (G : Type*) [Group G] [Finite G], undirectedCIGroup G →
  ∀ (H : Subgroup G), letI : Fintype H := Fintype.ofFinite H; undirectedCIGroup H
def claim28358 : Prop := ∀ p r : ℕ, ∀ hp : Nat.Prime p, 3 < p → 2 * p + 3 ≤ r →
  letI : NeZero p := ⟨hp.ne_zero⟩
  ¬ undirectedCIGroup (elementaryAbelian p r)

end
end MathlibPlus.Open.GroupTheory.NR2FormalizationDrain
