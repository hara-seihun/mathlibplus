import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace MathlibPlus.Combinatorics.Claim42341

/-- Claim 42341: deleting an explicitly present empty member of a finite family
of finite sets preserves its nonempty inclusion-minimal members and every
coordinate frequency. -/
theorem emptySetDeletionPreservesMinimaAndFrequencies
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (_hEmpty : ∅ ∈ F) :
    (∀ A : Finset α, A.Nonempty →
      ((A ∈ F.erase ∅ ∧
          ∀ B ∈ F.erase ∅, B.Nonempty → B ⊆ A → B = A) ↔
        (A ∈ F ∧
          ∀ B ∈ F, B.Nonempty → B ⊆ A → B = A))) ∧
    (∀ x : α,
      ((F.erase ∅).filter (fun A => x ∈ A)).card =
        (F.filter (fun A => x ∈ A)).card) := by
  constructor
  · intro A hA
    have hAne : A ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hA
    constructor
    · rintro ⟨hAerase, hmin⟩
      refine ⟨?_, ?_⟩
      · exact (Finset.mem_erase.mp hAerase).2
      · intro B hBinF hB hBsub
        have hBne : B ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hB
        apply hmin B (Finset.mem_erase.mpr ⟨hBne, hBinF⟩) hB hBsub
    · rintro ⟨hAF, hmin⟩
      refine ⟨Finset.mem_erase.mpr ⟨hAne, hAF⟩, ?_⟩
      intro B hBerase hB hBsub
      apply hmin B (Finset.mem_erase.mp hBerase).2 hB hBsub
  · intro x
    have hfilter :
        (F.erase ∅).filter (fun A => x ∈ A) =
          F.filter (fun A => x ∈ A) := by
      ext A
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨(Finset.mem_erase.mp h.1).2, h.2⟩
      · intro h
        have hAne : A ≠ ∅ := by
          intro hzero
          subst A
          simpa using h.2
        exact ⟨Finset.mem_erase.mpr ⟨hAne, h.1⟩, h.2⟩
    rw [hfilter]

end MathlibPlus.Combinatorics.Claim42341
