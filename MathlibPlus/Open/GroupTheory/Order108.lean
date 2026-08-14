import Mathlib

namespace MathlibPlus.Open.GroupTheory

abbrev C2SquaredTimesC3Cubed :=
  ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3 × ZMod 3

abbrev C2TimesC3Cubed :=
  ZMod 2 × ZMod 3 × ZMod 3 × ZMod 3

/-- Claim 39856: every order-two subgroup of `C₂² × C₃³` has a complementary
subgroup of type `C₂ × C₃³`, giving the stated direct-product decomposition. -/
def claim39856 : Prop :=
  Nat.card C2SquaredTimesC3Cubed = 108 ∧
    ∀ D : AddSubgroup C2SquaredTimesC3Cubed,
      Nat.card D = 2 →
        ∃ H : AddSubgroup C2SquaredTimesC3Cubed,
          Nat.card H = 54 ∧
            Nonempty (D ≃+ ZMod 2) ∧
            Nonempty (H ≃+ C2TimesC3Cubed) ∧
            D ⊓ H = ⊥ ∧
            D ⊔ H = ⊤ ∧
            Nonempty ((D × H) ≃+ C2SquaredTimesC3Cubed)

end MathlibPlus.Open.GroupTheory
