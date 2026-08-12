import Mathlib

/-!
# Global pairing cosets

The component projections of a cocycle form a `G`-set.  The exact coset
argument needs only that action and therefore is stated for an arbitrary group
action; specializing `Y` to the component-projection type gives the source
claim.
-/

namespace MathlibPlus.GroupTheory.GlobalPairingCoset

/-- If `σ₀` maps every left component projection to its right projection, all
such maps are the left coset of the common left-projection stabilizer. -/
theorem globalPairingCoset
    {G Y C : Type*} [Group G] [MulAction G Y]
    (R S : C → Y) (σ₀ : G)
    (hσ₀ : ∀ c, σ₀ • R c = S c) :
    {σ : G | ∀ c, σ • R c = S c} =
      (fun ρ : G => σ₀ * ρ) '' {ρ : G | ∀ c, ρ • R c = R c} := by
  ext σ
  constructor
  · intro hσ
    have hstab : ∀ c, (σ₀⁻¹ * σ) • R c = R c := by
      intro c
      rw [mul_smul, hσ c]
      have h' : R c = σ₀⁻¹ • S c := by
        simpa [smul_smul] using congrArg (fun y : Y => σ₀⁻¹ • y) (hσ₀ c)
      exact h'.symm
    refine ⟨σ₀⁻¹ * σ, hstab, ?_⟩
    simp
  · rintro ⟨ρ, hρ, rfl⟩ c
    rw [mul_smul, hρ c, hσ₀ c]

/-- The set of global pairings is empty or is a left coset of the
left-projection stabilizer. -/
theorem globalPairingEmptyOrCoset
    {G Y C : Type*} [Group G] [MulAction G Y]
    (R S : C → Y) :
    {σ : G | ∀ c, σ • R c = S c} = ∅ ∨
      ∀ σ₀, (∀ c, σ₀ • R c = S c) →
        {σ : G | ∀ c, σ • R c = S c} =
          (fun ρ : G => σ₀ * ρ) '' {ρ : G | ∀ c, ρ • R c = R c} := by
  by_cases h : ∃ σ : G, ∀ c, σ • R c = S c
  · right
    intro σ₀ hσ₀
    exact globalPairingCoset R S σ₀ hσ₀
  · left
    ext σ
    constructor
    · intro hσ
      exact False.elim (h ⟨σ, hσ⟩)
    · intro hσ
      exact False.elim (by simpa using hσ)

/-- In a finite group, a nonempty global-pairing coset has the same cardinality
as its component stabilizer. -/
theorem globalPairingCardEqStabilizer
    {G Y C : Type*} [Group G] [MulAction G Y] [Finite G]
    (R S : C → Y) (σ₀ : G)
    (hσ₀ : ∀ c, σ₀ • R c = S c) :
    Nat.card {σ : G // ∀ c, σ • R c = S c} =
      Nat.card {ρ : G // ∀ c, ρ • R c = R c} := by
  let e : {ρ : G // ∀ c, ρ • R c = R c} ≃
      {σ : G // ∀ c, σ • R c = S c} :=
    { toFun := fun ρ => ⟨σ₀ * ρ.1, by
          intro c
          rw [mul_smul, ρ.2 c, hσ₀ c]⟩
      invFun := fun σ => ⟨σ₀⁻¹ * σ.1, by
          intro c
          rw [mul_smul, σ.2 c]
          have h' : R c = σ₀⁻¹ • S c := by
            simpa [smul_smul] using congrArg (fun y : Y => σ₀⁻¹ • y) (hσ₀ c)
          exact h'.symm⟩
      left_inv := by
        intro ρ
        apply Subtype.ext
        simp
      right_inv := by
        intro σ
        apply Subtype.ext
        simp }
  exact Nat.card_congr e.symm

end MathlibPlus.GroupTheory.GlobalPairingCoset
