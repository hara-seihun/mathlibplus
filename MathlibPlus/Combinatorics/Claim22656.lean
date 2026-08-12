import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim22656

/-- A finite family of finite sets is union-closed. -/
def unionClosed {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∪ B ∈ 𝓕

/-- Number of members of a family containing a specified element. -/
def supportCount {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (x : α) : ℕ :=
  (𝓕.filter (fun A => x ∈ A)).card

/-- The usual nontriviality condition: the family has a nonempty member. -/
def hasNonemptyMember {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∃ A ∈ 𝓕, A.Nonempty

/-- Frankl's weak half-threshold assertion for finite nontrivial
union-closed families. -/
def weakFranklPrinciple (α : Type*) [DecidableEq α] : Prop :=
  ∀ 𝓕 : Finset (Finset α),
    𝓕.Nonempty → unionClosed 𝓕 → hasNonemptyMember 𝓕 →
      ∃ x : α, 2 * supportCount 𝓕 x ≥ 𝓕.card

/-- The strict formulation for families that do not contain the empty set. -/
def strictNoEmptyFranklPrinciple (α : Type*) [DecidableEq α] : Prop :=
  ∀ 𝓕 : Finset (Finset α),
    𝓕.Nonempty → ∅ ∉ 𝓕 → unionClosed 𝓕 → hasNonemptyMember 𝓕 →
      ∃ x : α, 2 * supportCount 𝓕 x > 𝓕.card

/-- Removing or adjoining the empty set changes neither a support count nor
union-closedness on the nonempty part, and converts weak half-threshold to
strict half-threshold. -/
theorem strictNoEmptyFrankl_iff_weakFrankl (α : Type*) [DecidableEq α] :
    strictNoEmptyFranklPrinciple α ↔ weakFranklPrinciple α := by
  constructor
  · intro hstrict 𝓕 hne hclosed hnonempty
    by_cases hempty : ∅ ∈ 𝓕
    · let 𝓖 := 𝓕.erase ∅
      have hGne : 𝓖.Nonempty := by
        rcases hnonempty with ⟨A, hA, hAnonempty⟩
        refine ⟨A, Finset.mem_erase.mpr ⟨?_, hA⟩⟩
        exact Finset.nonempty_iff_ne_empty.mp hAnonempty
      have hGnoempty : ∅ ∉ 𝓖 := by
        simp [𝓖]
      have hGclosed : unionClosed 𝓖 := by
        intro A B hA hB
        have hAne : A.Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro hA0
          exact hGnoempty (hA0 ▸ hA)
        have hBne : B.Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro hB0
          exact hGnoempty (hB0 ▸ hB)
        have hUnionF : A ∪ B ∈ 𝓕 := hclosed
          (Finset.mem_of_mem_erase hA) (Finset.mem_of_mem_erase hB)
        have hUnionne : (A ∪ B).Nonempty := by
          rcases hAne with ⟨a, ha⟩
          exact ⟨a, Finset.mem_union_left B ha⟩
        exact Finset.mem_erase.mpr
          ⟨Finset.nonempty_iff_ne_empty.mp hUnionne, hUnionF⟩
      have hGhas : hasNonemptyMember 𝓖 := by
        rcases hnonempty with ⟨A, hA, hAnonempty⟩
        exact ⟨A, Finset.mem_erase.mpr
          ⟨Finset.nonempty_iff_ne_empty.mp hAnonempty, hA⟩, hAnonempty⟩
      obtain ⟨x, hx⟩ := hstrict 𝓖 hGne hGnoempty hGclosed hGhas
      refine ⟨x, ?_⟩
      have hcount : supportCount 𝓖 x = supportCount 𝓕 x := by
        dsimp [𝓖, supportCount]
        rw [Finset.filter_erase]
        apply congrArg Finset.card
        apply Finset.erase_eq_of_notMem
        simp
      have hcardErase : 𝓖.card = 𝓕.card - 1 := by
        simpa [𝓖] using Finset.card_erase_of_mem hempty
      have hFcardpos : 0 < 𝓕.card := Finset.card_pos.mpr hne
      omega
    · obtain ⟨x, hx⟩ := hstrict 𝓕 hne hempty hclosed hnonempty
      exact ⟨x, le_of_lt hx⟩
  · intro hweak 𝓕 hne hnoempty hclosed hnonempty
    rcases hnonempty with ⟨A₀, hA₀, hA₀nonempty⟩
    obtain ⟨x, hx⟩ := hweak (insert ∅ 𝓕)
      (by simp)
      (by
        intro A B hA hB
        simp only [Finset.mem_insert] at hA hB
        rcases hA with rfl | hA <;> rcases hB with rfl | hB
        · simp
        · simpa using Finset.mem_insert_of_mem hB
        · simpa using Finset.mem_insert_of_mem hA
        · exact Finset.mem_insert_of_mem (hclosed hA hB))
      (by exact ⟨A₀, Finset.mem_insert_of_mem hA₀, hA₀nonempty⟩)
    refine ⟨x, ?_⟩
    have hcount : supportCount (insert ∅ 𝓕) x = supportCount 𝓕 x := by
      dsimp [supportCount]
      rw [Finset.filter_insert]
      simp
    have hcard : 𝓕.card + 1 = (insert ∅ 𝓕).card := by
      simpa [Nat.add_comm] using (Finset.card_insert_of_notMem hnoempty).symm
    omega

end MathlibPlus.Combinatorics.Claim22656
