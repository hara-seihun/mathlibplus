import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/--
Claim 20023.  `F` and `G` are the two factor families.  When the two
families contain the two toggle pairs at a coordinate absent from the base
sets, the three source tuples are distinct members of `F × G` and have the
same union.
-/
theorem togglePairsForceThreeToOneCollision_claim20023
    {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) (A B : Finset α) (x : α)
    (hA : A ∈ F) (hAx : A ∪ {x} ∈ F)
    (hB : B ∈ G) (hBx : B ∪ {x} ∈ G)
    (hx : x ∉ A ∪ B) :
    let t₁ : Finset α × Finset α := (A ∪ {x}, B)
    let t₂ : Finset α × Finset α := (A, B ∪ {x})
    let t₃ : Finset α × Finset α := (A ∪ {x}, B ∪ {x})
    t₁ ∈ F.product G ∧ t₂ ∈ F.product G ∧ t₃ ∈ F.product G ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ ∧
      t₁.1 ∪ t₁.2 = t₂.1 ∪ t₂.2 ∧
      t₂.1 ∪ t₂.2 = t₃.1 ∪ t₃.2 := by
  dsimp
  have hxA : x ∉ A := by
    intro h
    exact hx (Finset.mem_union_left B h)
  have hxB : x ∉ B := by
    intro h
    exact hx (Finset.mem_union_right A h)
  have hAB : A ∪ {x} ≠ A := by
    intro h
    have hmem : x ∈ A ∪ {x} := by simp
    rw [h] at hmem
    exact hxA hmem
  have hBA : B ∪ {x} ≠ B := by
    intro h
    have hmem : x ∈ B ∪ {x} := by simp
    rw [h] at hmem
    exact hxB hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨hAx, hB⟩
  · exact Finset.mem_product.mpr ⟨hA, hBx⟩
  · exact Finset.mem_product.mpr ⟨hAx, hBx⟩
  · intro h
    have hfst := congrArg Prod.fst h
    exact hAB hfst
  · intro h
    have hsnd := congrArg Prod.snd h
    exact hBA hsnd.symm
  · intro h
    have hfst := congrArg Prod.fst h
    exact hAB hfst.symm
  · simp [Finset.union_comm]
  · simp [Finset.union_comm]

/--
The final sentence of claim 20023: an injective union product on the two
factor families cannot contain both toggle pairs at one shared coordinate.
-/
theorem togglePairsForbidInjectiveProduct_claim20023
    {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) (A B : Finset α) (x : α)
    (hA : A ∈ F) (hAx : A ∪ {x} ∈ F)
    (hB : B ∈ G) (hBx : B ∪ {x} ∈ G)
    (hx : x ∉ A ∪ B)
    (hinj : ∀ {A₁ A₂ B₁ B₂ : Finset α},
      A₁ ∈ F → A₂ ∈ F → B₁ ∈ G → B₂ ∈ G →
      A₁ ∪ B₁ = A₂ ∪ B₂ → A₁ = A₂ ∧ B₁ = B₂) :
    False := by
  have hne : (A ∪ {x}, B) ≠ (A, B ∪ {x}) := by
    intro h
    have hxA : x ∉ A := by
      intro h'
      exact hx (Finset.mem_union_left B h')
    have hfst := congrArg Prod.fst h
    have hfst' : A ∪ {x} = A := by simpa using hfst
    have hxmem : x ∈ A ∪ {x} := by simp
    rw [hfst'] at hxmem
    exact hxA hxmem
  have heq : (A ∪ {x}) ∪ B = A ∪ (B ∪ {x}) := by
    simp [Finset.union_comm]
  have hpair := hinj hAx hA hB hBx heq
  exact hne (Prod.ext hpair.1 hpair.2)

end MathlibPlus.Combinatorics
