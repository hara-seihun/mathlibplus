import Mathlib

namespace MathlibPlus.Combinatorics.Claim42089

/-- A transitive orbit of distinct blocks has uniform incidence counts.  The
hypothesis `htransport` is the explicit block-orbit transport supplied by the
source action. -/
theorem uniformOrbitIncidence_claim42089
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (B : Finset β) (inc : α → β → Prop) [DecidableRel inc]
    (htransport : ∀ x y : α, ∃ e : β ≃ β,
      (∀ b, b ∈ B ↔ e b ∈ B) ∧
        (∀ b, inc x b ↔ inc y (e b))) :
    ∀ x y : α,
      (B.filter (fun b => inc x b)).card =
        (B.filter (fun b => inc y b)).card := by
  intro x y
  obtain ⟨e, heB, heinc⟩ := htransport x y
  let s := B.filter (fun b => inc x b)
  let t := B.filter (fun b => inc y b)
  have hi : ∀ (b : β) (hb : b ∈ s), e b ∈ t := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    apply Finset.mem_filter.mpr
    constructor
    · exact (heB b).mp hb'.1
    · exact (heinc b).mp hb'.2
  have hinj : ∀ (b₁ : β) (hb₁ : b₁ ∈ s) (b₂ : β) (hb₂ : b₂ ∈ s),
      e b₁ = e b₂ → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ h
    exact e.injective h
  have hsurj : ∀ (c : β) (hc : c ∈ t),
      ∃ b, ∃ (hb : b ∈ s), e b = c := by
    intro c hc
    have hc' := Finset.mem_filter.mp hc
    refine ⟨e.symm c, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (heB (e.symm c)).mpr
      simpa using hc'.1
    · apply (heinc (e.symm c)).mpr
      simpa using hc'.2
  exact Finset.card_bij (fun b _ => e b) hi hinj hsurj

end MathlibPlus.Combinatorics.Claim42089
