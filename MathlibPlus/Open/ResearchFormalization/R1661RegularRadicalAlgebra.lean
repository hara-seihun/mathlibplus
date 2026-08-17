import MathlibPlus.Open.ResearchFormalization.R1661ScalarPowerRepair

namespace MathlibPlus.Open.ResearchFormalization.R1661RegularRadicalAlgebra

open MathlibPlus.Open.Research
open MathlibPlus.Open.ResearchFormalization.R1661ScalarPowerRepair

/-- A linear equivalence normalizes an affine permutation subgroup when its
conjugation preserves exactly the subgroup. -/
def linearNormalizer {p : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (T : Subgroup (Equiv.Perm V)) (L : V ≃ₗ[ZMod p] V) : Prop :=
  ∀ g : Equiv.Perm V,
    g ∈ T ↔
      (L.toAddEquiv.toEquiv) * g * (L.toAddEquiv.toEquiv)⁻¹ ∈ T

/-- Preservation of the multiplication in the radical-algebra presentation is
algebra-automorphism action because `L` is already a `ZMod p`-linear
bijection. -/
def algebraAutomorphismAction {p : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (mul : V → V → V) (L : V ≃ₗ[ZMod p] V) : Prop :=
  ∀ x y : V, L (mul x y) = mul (L x) (L y)

/-- Claim 33031: over the prime field, every regular elementary-abelian affine
subgroup has the displayed commutative associative radical-algebra circle
presentation, and every linear normalizer acts as an algebra automorphism. -/
def claim33031 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V],
      ∀ (T : Subgroup (Equiv.Perm V)),
        (∀ t : T, fpAffine (p := p) t.1) →
        MathlibPlus.Open.Research.R1661.isRegular T →
        MathlibPlus.Open.Research.R1661.isElementaryAbelian p T →
        ∃ mul : V → V → V,
          radicalAlgebraPresentation (p := p) T mul ∧
            ∀ (L : V ≃ₗ[ZMod p] V),
              linearNormalizer T L →
              algebraAutomorphismAction mul L

end MathlibPlus.Open.ResearchFormalization.R1661RegularRadicalAlgebra
