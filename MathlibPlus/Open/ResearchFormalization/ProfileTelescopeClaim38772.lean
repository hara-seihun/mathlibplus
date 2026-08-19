import MathlibPlus.Open.ResearchFormalization.ProfileClaims
import MathlibPlus.Algebra.TranslationPeriod

namespace MathlibPlus.Open.ResearchFormalization.ProfileTelescopeClaims

open MathlibPlus.Open.ResearchFormalization.ProfileClaims

/-- Claim 38772: the profile rows on a cyclic base subgroup descend to the
aperiodic translation quotient and are forced to be successive translations. -/
def claim_38772 : Prop :=
  ∀ {B : Type*} {H : Type*} [AddCommGroup B] [Group H]
    [Fintype B] [Fintype H]
    (p : H → Equiv.Perm B) (a : H) (m : ℕ),
    p 1 = Equiv.refl B → orderOf a = m →
    ∀ (S : Set (B × H)), derivativeInvariant p S →
      let X := fiberSection S a
      let P := MathlibPlus.Algebra.TranslationPeriod.periodSubgroup X
      let q : B →+ (B ⧸ P) := QuotientAddGroup.mk' P
      let Y : Set (B ⧸ P) := q '' X
      let cbar := q (p (a⁻¹) 0)
      ∃ β : ℕ → Equiv.Perm (B ⧸ P),
        (∀ j : ℕ, j ≤ m → ∀ x : B,
          β j (q x) = q (p (a ^ j) x)) ∧
        β 0 = Equiv.refl (B ⧸ P) ∧
        β m = Equiv.refl (B ⧸ P) ∧
        (∀ j : ℕ, j < m → ∀ t : B ⧸ P,
          Set.image (β (j + 1))
              (MathlibPlus.Algebra.TranslationPeriod.translateSet Y t) =
            MathlibPlus.Algebra.TranslationPeriod.translateSet
              (MathlibPlus.Algebra.TranslationPeriod.translateSet Y (-cbar))
              (β j t)) ∧
        (∀ j : ℕ, j ≤ m → ∀ z : B ⧸ P,
          β j z = z + -(j • cbar)) ∧
        m • cbar = 0

end MathlibPlus.Open.ResearchFormalization.ProfileTelescopeClaims
