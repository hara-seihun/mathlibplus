import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch

structure ResearchAdditiveCharacter (V : Type*) [AddMonoid V] where
  toFun : V → ℂ
  map_zero' : toFun 0 = 1
  map_add' : ∀ x y : V, toFun (x + y) = toFun x * toFun y

instance {V : Type*} [AddMonoid V] : CoeFun (ResearchAdditiveCharacter V) (fun _ => V → ℂ) :=
  ⟨ResearchAdditiveCharacter.toFun⟩

def researchCharacterNontrivial {V : Type*} [AddMonoid V]
    (χ : ResearchAdditiveCharacter V) : Prop :=
  ∃ x : V, χ x ≠ 1

noncomputable def researchFourierCoefficient
    {V : Type*} [AddMonoid V] (F : Finset V)
    (χ : ResearchAdditiveCharacter V) : ℂ :=
  F.sum (fun x => χ x)

noncomputable def FourierRectangularity
    (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Fintype V]
    (F : Finset V) : Prop :=
  (∀ χ : ResearchAdditiveCharacter V,
      researchCharacterNontrivial χ → researchFourierCoefficient F χ = 0) ↔
    (F = ∅ ∨ F = Finset.univ)

end MathlibPlus.Open.ResearchBatch
