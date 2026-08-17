import Mathlib

namespace MathlibPlus.Open.GroupTheory

noncomputable section

/-- Claim 31838: the normalized one-coordinate functions over `F₅` have the
exact five-row census by the rank of the actual derivative module, affineness
of that generated image, actual-image conjugacy, and raw two-closure shear
membership. -/
def exactSixHundredTwentyFiveFunctionCensus_claim31838 : Prop := by
  classical
  exact ∀ [Fact (Nat.Prime 5)],
    let F := ZMod 5
    let V := Fin 4 → F
    let delta : (V → F) → V → V → F :=
      fun f u v => f (v + u) - f v
    let translate : (V → F) → V → V → F :=
      fun h w v => h (v + w)
    let generators : (V → F) → Set (V → F) :=
      fun f => {h | h = (fun _ : V => (1 : F)) ∨
        ∃ u w : V, h = translate (delta f u) w}
    let M : (V → F) → Submodule F (V → F) :=
      fun f => Submodule.span F (generators f)
    let imageAffine : (V → F) → Prop :=
      fun f => ∀ h : V → F, h ∈ M f →
        ∃ a : V →ᵃ[F] F, ∀ v : V, h v = a v
    let actualConjugate : (V → F) → Prop :=
      fun f => ∃ h : V → F, h ∈ M f ∧
        ∃ a : V →ᵃ[F] F, ∀ v : V, f v = h v + a v
    let rawShearInTwoClosure : (V → F) → Prop :=
      fun f => ∀ v : V,
        (∀ h : V → F, h ∈ M f → h v = h 0) → f v = 0
    let normalized : (F → F) → Prop := fun g => g 0 = 0
    let lift : (F → F) → V → F := fun g v => g (v 0)
    let row1 : (F → F) → Prop := fun g =>
      normalized g ∧ Module.finrank F (M (lift g)) = 1 ∧
        imageAffine (lift g) ∧ actualConjugate (lift g) ∧
        ¬ rawShearInTwoClosure (lift g)
    let row2 : (F → F) → Prop := fun g =>
      normalized g ∧ Module.finrank F (M (lift g)) = 1 ∧
        imageAffine (lift g) ∧ actualConjugate (lift g) ∧
        rawShearInTwoClosure (lift g)
    let row3 : (F → F) → Prop := fun g =>
      normalized g ∧ Module.finrank F (M (lift g)) = 2 ∧
        imageAffine (lift g) ∧ ¬ actualConjugate (lift g) ∧
        rawShearInTwoClosure (lift g)
    let row4 : (F → F) → Prop := fun g =>
      normalized g ∧ Module.finrank F (M (lift g)) = 3 ∧
        ¬ imageAffine (lift g) ∧ ¬ actualConjugate (lift g) ∧
        rawShearInTwoClosure (lift g)
    let row5 : (F → F) → Prop := fun g =>
      normalized g ∧ Module.finrank F (M (lift g)) = 4 ∧
        ¬ imageAffine (lift g) ∧ ¬ actualConjugate (lift g) ∧
        rawShearInTwoClosure (lift g)
    (Finset.univ.filter normalized).card = 625 ∧
      (Finset.univ.filter row1).card = 4 ∧
      (Finset.univ.filter row2).card = 1 ∧
      (Finset.univ.filter row3).card = 20 ∧
      (Finset.univ.filter row4).card = 100 ∧
      (Finset.univ.filter row5).card = 500 ∧
      (∀ g : F → F, normalized g →
        row1 g ∨ row2 g ∨ row3 g ∨ row4 g ∨ row5 g)

end
end MathlibPlus.Open.GroupTheory
