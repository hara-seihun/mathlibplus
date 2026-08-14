import Mathlib

namespace MathlibPlus.Open.Research.R1220

noncomputable section

abbrev C3 := Multiplicative (ZMod 3)
abbrev D10 := DihedralGroup 5
abbrev G90 := (C3 × C3) × D10

def c3Factor : Subgroup G90 :=
  Subgroup.comap (MonoidHom.snd (C3 × C3) D10) ⊥

def d10Factor : Subgroup G90 :=
  Subgroup.comap (MonoidHom.fst (C3 × C3) D10) ⊥

def involutionGenerated : Subgroup G90 :=
  Subgroup.closure {g : G90 | g ≠ 1 ∧ g ^ 2 = 1}

def claim30268 : Prop :=
  (∀ P : Sylow 3 G90, (P : Subgroup G90) = c3Factor) ∧
  (∀ φ : G90 ≃* G90, Subgroup.map φ.toMonoidHom c3Factor = c3Factor) ∧
  involutionGenerated = d10Factor ∧
  (∀ φ : G90 ≃* G90, Subgroup.map φ.toMonoidHom d10Factor = d10Factor) ∧
  Nonempty ((G90 ≃* G90) ≃* (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) × (D10 ≃* D10))) ∧
  Fintype.card (G90 ≃* G90) = 48 * 20 ∧
  48 * 20 = 960

abbrev G90₀ := {g : G90 // g ≠ 1}

def invNonidentity (x : G90₀) : G90₀ :=
  ⟨(x : G90)⁻¹, inv_ne_one.mpr x.property⟩

def inverseAtom (x : G90₀) : Finset G90₀ := {x, invNonidentity x}

abbrev InverseAtom := {A : Finset G90₀ // ∃ x : G90₀, A = inverseAtom x}

def singletonInverseAtom (A : InverseAtom) : Prop := A.1.card = 1

def pairedInverseAtom (A : InverseAtom) : Prop := A.1.card = 2

def isReflection (g : G90) : Prop :=
  g.1 = 1 ∧ g.2 ≠ 1 ∧ g.2 ^ 2 = 1

def mapNonidentity (φ : G90 ≃* G90) (x : G90₀) : G90₀ :=
  ⟨φ (x : G90), by
    intro hx
    apply x.property
    apply φ.injective
    simpa using hx⟩

def mapInverseAtom (φ : G90 ≃* G90) (A : InverseAtom) : InverseAtom :=
  ⟨A.1.image (mapNonidentity φ), by
    rcases A.2 with ⟨x, hx⟩
    refine ⟨mapNonidentity φ x, ?_⟩
    rw [hx]
    ext y
    simp [inverseAtom, mapNonidentity, invNonidentity]⟩

instance : Fintype InverseAtom := Fintype.ofFinite InverseAtom
instance : Fintype {A : InverseAtom // singletonInverseAtom A} := Fintype.ofFinite _
instance : Fintype {A : InverseAtom // pairedInverseAtom A} := Fintype.ofFinite _

def claim30269 : Prop :=
  Fintype.card InverseAtom = 47 ∧
  Fintype.card {A : InverseAtom // singletonInverseAtom A} = 5 ∧
  Fintype.card {A : InverseAtom // pairedInverseAtom A} = 42 ∧
  (∀ A : InverseAtom, singletonInverseAtom A ∨ pairedInverseAtom A) ∧
  (∀ A : InverseAtom, singletonInverseAtom A →
    ∀ x ∈ A.1, isReflection (x : G90)) ∧
  (∀ φ ψ : G90 ≃* G90,
    (∀ A : InverseAtom, mapInverseAtom φ A = mapInverseAtom ψ A) → φ = ψ)

abbrev ConnectionSet := {S : Finset G90 // 1 ∉ S ∧ ∀ g, g ∈ S ↔ g⁻¹ ∈ S}

instance : Fintype ConnectionSet := Fintype.ofFinite ConnectionSet

noncomputable def cayleyGraph (S : ConnectionSet) : SimpleGraph G90 where
  Adj u v := u ≠ v ∧ u⁻¹ * v ∈ S.1
  symm := ⟨fun u v huv => by
    refine ⟨Ne.symm huv.1, ?_⟩
    have hi := (S.2.2 (u⁻¹ * v)).mp huv.2
    simpa [mul_inv_rev] using hi⟩
  loopless := ⟨fun u hu => hu.1 rfl⟩

def graphIsomorphic (S T : ConnectionSet) : Prop :=
  Nonempty ((cayleyGraph S).Iso (cayleyGraph T))

def automorphismImage (φ : G90 ≃* G90) (S : ConnectionSet) : ConnectionSet :=
  ⟨S.1.image φ, by
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨g, hg, hφ⟩
      have hg1 : g = 1 := φ.injective (by simpa using hφ)
      exact S.2.1 (hg1 ▸ hg)
    · intro g
      constructor
      · intro hg
        rcases Finset.mem_image.mp hg with ⟨x, hx, hφ⟩
        refine Finset.mem_image.mpr ⟨x⁻¹, (S.2.2 x).mp hx, ?_⟩
        simpa [hφ] using φ.map_inv x
      · intro hg
        rcases Finset.mem_image.mp hg with ⟨x, hx, hφ⟩
        refine Finset.mem_image.mpr ⟨x⁻¹, (S.2.2 x).mp hx, ?_⟩
        simpa [hφ] using φ.map_inv x⟩

instance : SMul (G90 ≃* G90) ConnectionSet := ⟨automorphismImage⟩

instance : MulAction (G90 ≃* G90) ConnectionSet where
  one_smul S := by
    apply Subtype.ext
    change S.1.image (1 : G90 ≃* G90) = S.1
    apply Finset.ext
    intro x
    simp [Finset.mem_image]
  mul_smul φ ψ S := by
    apply Subtype.ext
    change S.1.image (φ * ψ) = (S.1.image ψ).image φ
    rw [Finset.image_image]
    congr 1

def graphSetoid : Setoid ConnectionSet where
  r := graphIsomorphic
  iseqv := by
    constructor
    · intro S
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro S T h
      rcases h with ⟨h⟩
      exact ⟨h.symm⟩
    · intro S T U hST hTU
      rcases hST with ⟨hST⟩
      rcases hTU with ⟨hTU⟩
      exact ⟨RelIso.trans hST hTU⟩

def valency (S : ConnectionSet) : ℕ := S.1.card

abbrev valencySlice (k : ℕ) := {S : ConnectionSet // valency S = k}

instance (k : ℕ) : Fintype (valencySlice k) := Fintype.ofFinite _

def sliceAction (k : ℕ) (φ : G90 ≃* G90) (S : valencySlice k) : valencySlice k :=
  ⟨automorphismImage φ S.1, by
    have hc : (automorphismImage φ S.1).1.card = S.1.1.card :=
      Finset.card_image_of_injective _ φ.injective
    simpa [valency, hc] using S.2⟩

instance (k : ℕ) : SMul (G90 ≃* G90) (valencySlice k) :=
  ⟨sliceAction k⟩

instance (k : ℕ) : MulAction (G90 ≃* G90) (valencySlice k) where
  one_smul S := by
    apply Subtype.ext
    apply Subtype.ext
    change S.1.1.image (1 : G90 ≃* G90) = S.1.1
    apply Finset.ext
    intro x
    simp [Finset.mem_image]
  mul_smul φ ψ S := by
    apply Subtype.ext
    apply Subtype.ext
    change S.1.1.image (φ * ψ) = (S.1.1.image ψ).image φ
    rw [Finset.image_image]
    congr 1

instance (k : ℕ) : Fintype (Quotient (MulAction.orbitRel (G90 ≃* G90) (valencySlice k))) :=
  Fintype.ofFinite _

def graphSliceSetoid (k : ℕ) : Setoid (valencySlice k) where
  r S T := graphIsomorphic S.1 T.1
  iseqv := by
    constructor
    · intro S
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro S T h
      rcases h with ⟨h⟩
      exact ⟨h.symm⟩
    · intro S T U hST hTU
      rcases hST with ⟨hST⟩
      rcases hTU with ⟨hTU⟩
      exact ⟨RelIso.trans hST hTU⟩

noncomputable instance (k : ℕ) : Fintype (Quotient (graphSliceSetoid k)) :=
  Fintype.ofFinite _

def censusEntry (k raw orbitCount graphCount : ℕ) : Prop :=
  Fintype.card (valencySlice k) = raw ∧
  Fintype.card (Quotient (MulAction.orbitRel (G90 ≃* G90) (valencySlice k))) = orbitCount ∧
  Fintype.card (Quotient (graphSliceSetoid k)) = graphCount

def ciConnection (S : ConnectionSet) : Prop :=
  ∀ T : ConnectionSet, graphIsomorphic S T →
    ∃ φ : G90 ≃* G90, automorphismImage φ S = T

def connectionComplement (S : ConnectionSet) : ConnectionSet :=
  ⟨Finset.univ \ (insert 1 S.1), by
    constructor
    · simp
    · intro g
      constructor
      · intro hg
        have hnot : g ∉ insert 1 S.1 := (Finset.mem_sdiff.mp hg).2
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hnot (Finset.mem_insert.mpr (Or.inl (by simpa using h)))
        · exact hnot (Finset.mem_insert.mpr (Or.inr ((S.2.2 g).mpr h)))
      · intro hg
        have hnot : g⁻¹ ∉ insert 1 S.1 := (Finset.mem_sdiff.mp hg).2
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hnot (Finset.mem_insert.mpr (Or.inl (by simpa using h)))
        · exact hnot (Finset.mem_insert.mpr (Or.inr ((S.2.2 g).mp h)))⟩

def claim30275 : Prop :=
  ∀ S : ConnectionSet, 78 ≤ valency S ∧ valency S ≤ 89 → ciConnection S

def claim30277 : Prop :=
  censusEntry 12 14312116 24664 24664 ∧
  censusEntry 13 34847540 50286 50286 ∧
  (∀ S : valencySlice 12, ciConnection S.1) ∧
  (∀ S : valencySlice 13, ciConnection S.1)

def claim30278 : Prop :=
  (∀ S : ConnectionSet, valency S = 12 → ciConnection S) ∧
  (∀ S : ConnectionSet, valency S = 13 → ciConnection S) ∧
  (∀ S : ConnectionSet, valency S = 12 → ciConnection (connectionComplement S)) ∧
  (∀ S : ConnectionSet, valency S = 13 → ciConnection (connectionComplement S)) ∧
  (∀ S : ConnectionSet, valency S = 12 → valency (connectionComplement S) = 77) ∧
  (∀ S : ConnectionSet, valency S = 13 → valency (connectionComplement S) = 76)

def claim30270 : Prop :=
  censusEntry 0 1 1 1 ∧
  censusEntry 1 5 1 1 ∧
  censusEntry 2 52 5 5 ∧
  censusEntry 3 220 6 6 ∧
  censusEntry 4 1286 28 28 ∧
  censusEntry 5 4726 41 41 ∧
  censusEntry 6 20300 150 150 ∧
  censusEntry 7 66052 257 257 ∧
  censusEntry 8 231035 854 854 ∧
  censusEntry 9 675311 1609 1609 ∧
  censusEntry 10 2027368 4687 4687 ∧
  censusEntry 11 5384120 9382 9382 ∧
  (∑ k ∈ Finset.range 12, Fintype.card (valencySlice k)) = 8410476 ∧
  (∑ k ∈ Finset.range 12,
    Fintype.card (Quotient (MulAction.orbitRel (G90 ≃* G90) (valencySlice k)))) = 17021 ∧
  (∑ k ∈ Finset.range 12, Fintype.card (Quotient (graphSliceSetoid k))) = 17021

end
end MathlibPlus.Open.Research.R1220
