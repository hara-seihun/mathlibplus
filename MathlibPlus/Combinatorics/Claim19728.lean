import Mathlib

namespace MathlibPlus.Combinatorics.Claim19728

/-- A set with one more element cannot inject into a set of the smaller
cardinality.  This is the finite-cardinality core of the literal tight-pair
contradiction in claim 19728. -/
theorem noSuccEmbedding_claim19728 (a : ℕ) :
    ¬ Nonempty (Fin (a + 1) ↪ Fin a) := by
  rintro ⟨f⟩
  have hcard : Fintype.card (Fin (a + 1)) ≤ Fintype.card (Fin a) :=
    Fintype.card_le_of_injective f f.injective
  simp only [Fintype.card_fin] at hcard
  omega

/-- Exact tightness `a₀₀ = 1 + a₁₁` makes the attempted injection
impossible.  The family/core and the source-specific union map are not
reconstructed because they are not defined in the claim text. -/
theorem tightPairInjectionContradiction_claim19728
    (a₀₀ a₁₁ : ℕ) (htight : a₀₀ = 1 + a₁₁) :
    ¬ Nonempty (Fin a₀₀ ↪ Fin a₁₁) := by
  subst a₀₀
  simpa [Nat.add_comm] using noSuccEmbedding_claim19728 a₁₁

end MathlibPlus.Combinatorics.Claim19728
