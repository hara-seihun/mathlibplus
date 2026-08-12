import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim47189

/-!
Formalization of admitted claim 47189 (legacy packet R-2672).  A finite family
of finite sets is represented by `F : Finset (Finset α)`.  The trace fibre over
an outside support `S` is the image of the exact filter
`A \ M = S` under intersection with `M`; no additional trace convention is
introduced.
-/

/-- The trace fibre over `S` contains `M` whenever it is nonempty; trace unions
    land in the fibre over the union of the outside supports; and the support
    family is union-closed. -/
theorem traceFibres_unionClosed
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α)
    (hM : M ∈ F) (_hMcard : M.card = 3)
    (hUnion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) :
    let H : Finset α → Finset (Finset α) :=
      fun S => (F.filter (fun A => A \ M = S)).image (fun A => A ∩ M)
    (∀ S : Finset α, (H S).Nonempty → M ∈ H S) ∧
      (∀ S T U V : Finset α, U ∈ H S → V ∈ H T → U ∪ V ∈ H (S ∪ T)) ∧
      (∀ S T : Finset α, (H S).Nonempty → (H T).Nonempty →
        (H (S ∪ T)).Nonempty) := by
  dsimp
  have hdiff_right : ∀ A M : Finset α, (A ∪ M) \ M = A \ M := by
    intro A M'
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hA | hM', hnM⟩
      · exact ⟨hA, hnM⟩
      · exact False.elim (hnM hM')
    · rintro ⟨hA, hnM⟩
      exact ⟨Or.inl hA, hnM⟩
  have hinter_right : ∀ A M : Finset α, (A ∪ M) ∩ M = M := by
    intro A M'
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨_, hM'⟩
      exact hM'
    · intro hM'
      exact ⟨Or.inr hM', hM'⟩
  have hdiff_union : ∀ A B M : Finset α,
      (A ∪ B) \ M = (A \ M) ∪ (B \ M) := by
    intro A B M'
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hA | hB, hnM⟩
      · exact Or.inl ⟨hA, hnM⟩
      · exact Or.inr ⟨hB, hnM⟩
    · intro h
      rcases h with hA | hB
      · exact ⟨Or.inl hA.1, hA.2⟩
      · exact ⟨Or.inr hB.1, hB.2⟩
  have hinter_union : ∀ A B M : Finset α,
      (A ∪ B) ∩ M = (A ∩ M) ∪ (B ∩ M) := by
    intro A B M'
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hA | hB, hM'⟩
      · exact Or.inl ⟨hA, hM'⟩
      · exact Or.inr ⟨hB, hM'⟩
    · intro h
      rcases h with hA | hB
      · exact ⟨Or.inl hA.1, hA.2⟩
      · exact ⟨Or.inr hB.1, hB.2⟩
  have htrace : ∀ S T U V : Finset α,
      U ∈ (F.filter (fun A => A \ M = S)).image (fun A => A ∩ M) →
      V ∈ (F.filter (fun A => A \ M = T)).image (fun A => A ∩ M) →
      U ∪ V ∈ (F.filter (fun A => A \ M = S ∪ T)).image (fun A => A ∩ M) := by
    intro S T U V hU hV
    rcases Finset.mem_image.mp hU with ⟨A, hA, hAU⟩
    rcases Finset.mem_image.mp hV with ⟨B, hB, hBV⟩
    have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
    have hAS : A \ M = S := (Finset.mem_filter.mp hA).2
    have hBF : B ∈ F := (Finset.mem_filter.mp hB).1
    have hBT : B \ M = T := (Finset.mem_filter.mp hB).2
    have hABF : A ∪ B ∈ F := hUnion A hAF B hBF
    apply Finset.mem_image.mpr
    refine ⟨A ∪ B, Finset.mem_filter.mpr ⟨hABF, ?_⟩, ?_⟩
    · rw [hdiff_union, hAS, hBT]
    · calc
        (A ∪ B) ∩ M = (A ∩ M) ∪ (B ∩ M) := hinter_union A B M
        _ = U ∪ V := by rw [hAU, hBV]
  constructor
  · intro S hS
    rcases Finset.nonempty_def.mp hS with ⟨T, hT⟩
    rcases Finset.mem_image.mp hT with ⟨A, hA, _hAT⟩
    have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
    have hAS : A \ M = S := (Finset.mem_filter.mp hA).2
    have hAM : A ∪ M ∈ F := hUnion A hAF M hM
    apply Finset.mem_image.mpr
    refine ⟨A ∪ M, Finset.mem_filter.mpr ⟨hAM, ?_⟩, ?_⟩
    · rw [hdiff_right, hAS]
    · exact hinter_right A M
  · constructor
    · exact htrace
    · intro S T hS hT
      rcases Finset.nonempty_def.mp hS with ⟨U, hU⟩
      rcases Finset.nonempty_def.mp hT with ⟨V, hV⟩
      exact ⟨U ∪ V, htrace S T U V hU hV⟩

end MathlibPlus.Combinatorics.Claim47189
