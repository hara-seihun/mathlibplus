-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.GraphTheory.Claim38511

open scoped Pointwise

noncomputable section

private theorem addCayley_connectionComplement
    {G : Type*} [AddGroup G] (S : Set G)
    (hSinv : ∀ x, x ∈ S ↔ -x ∈ S) :
    SimpleGraph.addCayley ({x : G | x ≠ 0 ∧ x ∉ S}) =
      (SimpleGraph.addCayley S)ᶜ := by
  ext x y
  rw [SimpleGraph.compl_adj, SimpleGraph.addCayley_adj,
    SimpleGraph.addCayley_adj]
  constructor
  · rintro ⟨hxy, hmem⟩
    refine ⟨hxy, ?_⟩
    intro hadj
    rcases hmem with hmem | hmem
    · exact hmem.2 (hadj.2.elim id fun hyx => by
        exact (hSinv (-x + y)).mpr (by simpa [add_comm] using hyx))
    · exact hmem.2 (hadj.2.elim (fun hxy' => by
        exact (hSinv (-y + x)).mpr (by simpa [add_comm] using hxy')) id)
  · rintro ⟨hxy, hnot⟩
    refine ⟨hxy, Or.inl ⟨?_, ?_⟩⟩
    · intro hzero
      have hxyeq : x = y := neg_add_eq_zero.mp hzero
      exact hxy (sub_eq_zero.mp (sub_eq_zero.mpr hxyeq.symm)).symm
    · intro hmem
      exact hnot ⟨hxy, Or.inl hmem⟩

private theorem nonempty_iso_connectionComplement_iff
    {G : Type*} [AddGroup G] (S T : Set G)
    (hSinv : ∀ x, x ∈ S ↔ -x ∈ S)
    (hTinv : ∀ x, x ∈ T ↔ -x ∈ T) :
    Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) ↔
      Nonempty
        (SimpleGraph.addCayley {x : G | x ≠ 0 ∧ x ∉ S} ≃g
          SimpleGraph.addCayley {x : G | x ≠ 0 ∧ x ∉ T}) := by
  rw [addCayley_connectionComplement S hSinv,
    addCayley_connectionComplement T hTinv]
  constructor
  · rintro ⟨e⟩
    refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
    intro x y
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    exact and_congr e.injective.ne_iff e.map_rel_iff.not
  · rintro ⟨e⟩
    let ec : (SimpleGraph.addCayley S)ᶜᶜ ≃g
        (SimpleGraph.addCayley T)ᶜᶜ :=
      { toEquiv := e.toEquiv
        map_rel_iff' := by
          intro x y
          rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
          exact and_congr e.injective.ne_iff e.map_rel_iff.not }
    exact ⟨by simpa using ec⟩

private theorem addEquiv_image_connectionComplement_iff
    {G : Type*} [AddGroup G] (φ : G ≃+ G) (S T : Set G)
    (hSzero : 0 ∉ S) (hTzero : 0 ∉ T) :
    φ '' {x : G | x ≠ 0 ∧ x ∉ S} = {x : G | x ≠ 0 ∧ x ∉ T} ↔
      φ '' S = T := by
  let A : Set G := Set.univ \ {0}
  have hA : φ '' A = A := by
    dsimp [A]
    rw [Set.image_sdiff φ.injective]
    simp
  have hSsub : S ⊆ A := by
    intro x hx
    simp only [A, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    intro hx0
    exact hSzero (hx0 ▸ hx)
  have hTsub : T ⊆ A := by
    intro x hx
    simp only [A, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    intro hx0
    exact hTzero (hx0 ▸ hx)
  have hbarS : ({x : G | x ≠ 0 ∧ x ∉ S}) = A \ S := by
    ext x
    simp [A]
  have hbarT : ({x : G | x ≠ 0 ∧ x ∉ T}) = A \ T := by
    ext x
    simp [A]
  rw [hbarS, hbarT]
  constructor
  · intro hcomp
    have hφSsub : φ '' S ⊆ A := by
      rw [← hA]
      exact Set.image_mono hSsub
    have hdiff : A \ (φ '' S) = A \ T := by
      calc
        A \ (φ '' S) = (φ '' A) \ (φ '' S) := by rw [hA]
        _ = φ '' (A \ S) := (Set.image_sdiff φ.injective A S).symm
        _ = A \ T := hcomp
    ext y
    by_cases hyA : y ∈ A
    · have hy := Set.ext_iff.mp hdiff y
      simp only [Set.mem_sdiff, hyA, true_and] at hy
      tauto
    · have hyS : y ∉ φ '' S := fun hy => hyA (hφSsub hy)
      have hyT : y ∉ T := fun hy => hyA (hTsub hy)
      simp [hyS, hyT]
  · intro hφ
    rw [Set.image_sdiff φ.injective, hφ, hA]

theorem complementValency15To56_claim38511 :
    let G := (Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)
    (∀ S T : Set G,
      0 ∉ S → 0 ∉ T →
      (∀ x, x ∈ S ↔ -x ∈ S) →
      (∀ x, x ∈ T ↔ -x ∈ T) →
      S.ncard = 15 → T.ncard = 15 →
      Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
      ∃ α : G ≃+ G, α '' S = T) →
    ∀ S T : Set G,
      0 ∉ S → 0 ∉ T →
      (∀ x, x ∈ S ↔ -x ∈ S) →
      (∀ x, x ∈ T ↔ -x ∈ T) →
      S.ncard = 56 → T.ncard = 56 →
      Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
      ∃ α : G ≃+ G, α '' S = T := by
  dsimp
  have hcard : Fintype.card ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)) = 72 := by
    native_decide
  intro h15 S T hSzero hTzero hSinv hTinv hScard hTcard he
  let Sbar : Set ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)) :=
    {x | x ≠ 0 ∧ x ∉ S}
  let Tbar : Set ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)) :=
    {x | x ≠ 0 ∧ x ∉ T}
  have hSsub : S ⊆ ({0} : Set ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)))ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx0
    apply hSzero
    simpa [hx0] using hx
  have hTsub : T ⊆ ({0} : Set ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)))ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx0
    apply hTzero
    simpa [hx0] using hx
  have hSbarEq : Sbar = ({0} : Set ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)))ᶜ \ S := by
    ext x
    simp [Sbar]
  have hTbarEq : Tbar = ({0} : Set ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)))ᶜ \ T := by
    ext x
    simp [Tbar]
  have hSbarCard : Sbar.ncard = 15 := by
    rw [hSbarEq, Set.ncard_sdiff hSsub, Set.ncard_compl]
    simp [hcard, hScard]
  have hTbarCard : Tbar.ncard = 15 := by
    rw [hTbarEq, Set.ncard_sdiff hTsub, Set.ncard_compl]
    simp [hcard, hTcard]
  have hSbar0 : 0 ∉ Sbar := by
    simp [Sbar]
  have hTbar0 : 0 ∉ Tbar := by
    simp [Tbar]
  have hSbarInv : ∀ x, x ∈ Sbar ↔ -x ∈ Sbar := by
    intro x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro hz
        exact hx.1 (by simpa using neg_eq_zero.mp hz)
      · intro hneg
        exact hx.2 ((hSinv x).mpr (by simpa using hneg))
    · intro hx
      refine ⟨?_, ?_⟩
      · intro hz
        apply hx.1
        simpa [hz]
      · intro hpos
        exact hx.2 ((hSinv (-x)).mpr (by simpa using hpos))
  have hTbarInv : ∀ x, x ∈ Tbar ↔ -x ∈ Tbar := by
    intro x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro hz
        exact hx.1 (by simpa using neg_eq_zero.mp hz)
      · intro hneg
        exact hx.2 ((hTinv x).mpr (by simpa using hneg))
    · intro hx
      refine ⟨?_, ?_⟩
      · intro hz
        apply hx.1
        simpa [hz]
      · intro hpos
        exact hx.2 ((hTinv (-x)).mpr (by simpa using hpos))
  have hbarIso :
      Nonempty (SimpleGraph.addCayley Sbar ≃g SimpleGraph.addCayley Tbar) := by
    simpa [Sbar, Tbar] using
      (nonempty_iso_connectionComplement_iff S T hSinv hTinv).mp he
  obtain ⟨α, hα⟩ := h15 Sbar Tbar hSbar0 hTbar0 hSbarInv hTbarInv
    hSbarCard hTbarCard hbarIso
  have hImage := addEquiv_image_connectionComplement_iff α S T hSzero hTzero
  refine ⟨α, ?_⟩
  apply (hImage).mp
  change α '' Sbar = Tbar
  exact hα

end
end MathlibPlus.GraphTheory.Claim38511
