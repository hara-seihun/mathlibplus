import Mathlib

namespace MathlibPlus.GroupTheory

/--
For a finite family of inverse-pair atoms, the number of atoms whose elements
have order `n` is unchanged by a group automorphism.  The explicit inverse-pair
hypothesis records the source meaning of an atom; the proof is valid for the
slightly larger class of finite families of finite subsets as well.
-/
theorem elementOrderProfile_automorphism_invariant_claim6557
    {G : Type*} [Fintype G] [CommGroup G] [DecidableEq G]
    (I : Finset (Finset G))
    (_hI : ∀ A ∈ I, ∃ d : G, A = {d, d⁻¹})
    (e : G ≃* G) (n : ℕ) :
    let profile : Finset (Finset G) → ℕ → ℕ :=
      fun J k => (J.filter (fun A => ∀ a ∈ A, orderOf a = k)).card
    profile (I.image (fun A => A.image e)) n = profile I n := by
  classical
  dsimp
  have hp : ∀ A : Finset G,
      (∀ a ∈ A.image e, orderOf a = n) ↔ (∀ a ∈ A, orderOf a = n) := by
    intro A
    constructor
    · intro h a ha
      have hea : e a ∈ A.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa using h (e a) hea
    · intro h b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      simpa using h a ha
  rw [Finset.filter_image]
  have hfilter :
      I.filter (fun A => ∀ a ∈ A.image e, orderOf a = n) =
        I.filter (fun A => ∀ a ∈ A, orderOf a = n) := by
    apply Finset.filter_congr
    intro A hA
    exact hp A
  rw [hfilter]
  apply Finset.card_image_iff.mpr
  intro A hA B hB hEq
  change A.image e = B.image e at hEq
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have hmem : e a ∈ A.image e := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [hEq] at hmem
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
    exact e.injective hba ▸ hb
  · intro hb
    have hmem : e a ∈ B.image e := Finset.mem_image.mpr ⟨a, hb, rfl⟩
    rw [← hEq] at hmem
    obtain ⟨b, hA', hba⟩ := Finset.mem_image.mp hmem
    exact e.injective hba ▸ hA'

end MathlibPlus.GroupTheory
