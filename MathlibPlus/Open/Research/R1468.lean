import Mathlib

namespace MathlibPlus.Open.Research.R1468

abbrev CayleyGroup := (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3)

/-- The inverse-closed, identity-free connection sets of a prescribed valency. -/
def ConnectionSet (k : ℕ) :=
  {S : Finset CayleyGroup //
    0 ∉ S ∧ (∀ x : CayleyGroup, x ∈ S ↔ -x ∈ S) ∧ S.card = k}

instance connectionSetFinite (k : ℕ) : Finite (ConnectionSet k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance connectionSetFintype (k : ℕ) : Fintype (ConnectionSet k) :=
  Fintype.ofFinite (ConnectionSet k)

/-- The adjacency relation of the undirected Cayley graph determined by `S`. -/
def cayleyAdj (S : Finset CayleyGroup) (x y : CayleyGroup) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Ordinary graph isomorphism between two Cayley graphs on the labelled group. -/
def graphEquivalent {k : ℕ} (S T : ConnectionSet k) : Prop :=
  ∃ e : CayleyGroup ≃ CayleyGroup,
    ∀ x y : CayleyGroup,
      cayleyAdj S.1 x y ↔ cayleyAdj T.1 (e x) (e y)

/-- Equivalence by a group automorphism of the Cayley group. -/
def automorphismEquivalent {k : ℕ} (S T : ConnectionSet k) : Prop :=
  ∃ e : CayleyGroup ≃+ CayleyGroup, S.1.image e = T.1

def presentationSetoid (k : ℕ) : Setoid (ConnectionSet k) where
  r := automorphismEquivalent
  iseqv := by
    constructor
    · intro S
      exact ⟨AddEquiv.refl CayleyGroup, by simp⟩
    · intro S T h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨y, hyT, hxy⟩
        have hyImg : y ∈ S.1.image e := by
          rw [he]
          exact hyT
        rcases Finset.mem_image.mp hyImg with ⟨z, hz, hzy⟩
        have hxz : x = z := by
          calc
            x = e.symm y := hxy.symm
            _ = e.symm (e z) := by rw [hzy]
            _ = z := by simp
        simpa [hxz] using hz
      · intro hx
        have hyT : e x ∈ T.1 := by
          rw [← he]
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        exact Finset.mem_image.mpr ⟨e x, hyT, by simp⟩
    · intro S T U hST hTU
      rcases hST with ⟨e, he⟩
      rcases hTU with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      calc
        S.1.image (e.trans f) = (S.1.image e).image f := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
            apply Finset.mem_image.mpr ⟨e a, ?_, ?_⟩
            · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
            · simpa using hax
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨b, hb, hbx⟩
            rcases Finset.mem_image.mp hb with ⟨a, ha, hab⟩
            apply Finset.mem_image.mpr ⟨a, ha, ?_⟩
            simpa [hab] using hbx
        _ = U.1 := by rw [he, hf]

def graphSetoid (k : ℕ) : Setoid (ConnectionSet k) where
  r := graphEquivalent
  iseqv := by
    constructor
    · intro S
      exact ⟨Equiv.refl CayleyGroup, by simp⟩
    · intro S T h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      simpa using (he (e.symm x) (e.symm y)).symm
    · intro S T U hST hTU
      rcases hST with ⟨e, he⟩
      rcases hTU with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro x y
      exact (he x y).trans (hf (e x) (e y))

/-- The valency-seventeen census and the assertion that graph fibres are exactly
presentation orbits. -/
def claim37540 : Prop :=
  Fintype.card (ConnectionSet 17) = 210664468 ∧
    (letI := Fintype.ofFinite (Quotient (presentationSetoid 17))
     Fintype.card (Quotient (presentationSetoid 17)) = 66311) ∧
    (letI := Fintype.ofFinite (Quotient (graphSetoid 17))
     Fintype.card (Quotient (graphSetoid 17)) = 66311) ∧
    ∀ S T : ConnectionSet 17,
      graphEquivalent S T ↔ automorphismEquivalent S T

/-- CI for undirected Cayley graphs, stated using the concrete group above. -/
def isCI (k : ℕ) : Prop :=
  ∀ S T : ConnectionSet k, graphEquivalent S T → automorphismEquivalent S T

def translation (a : CayleyGroup) : Equiv.Perm CayleyGroup where
  toFun x := x + a
  invFun x := x - a
  left_inv := by intro x; simp
  right_inv := by intro x; simp

def preservesGraph (S : ConnectionSet k) (e : Equiv.Perm CayleyGroup) : Prop :=
  ∀ x y : CayleyGroup, cayleyAdj S.1 x y ↔ cayleyAdj S.1 (e x) (e y)

def regularOn (H : Subgroup (Equiv.Perm CayleyGroup)) : Prop :=
  ∀ x y : CayleyGroup, ∃! p : Equiv.Perm CayleyGroup, p ∈ H ∧ p x = y

def conjugatesToNaturalTranslations (S : ConnectionSet k)
    (H : Subgroup (Equiv.Perm CayleyGroup)) : Prop :=
  ∃ a : Equiv.Perm CayleyGroup,
    preservesGraph S a ∧
      ∀ p : Equiv.Perm CayleyGroup,
        p ∈ H ↔ ∃ b : CayleyGroup, a * p * a⁻¹ = translation b

/-- CI and the regular-subgroup Cayley-presentation consequence. -/
def claim37541 : Prop :=
  isCI 17 ∧
    ∀ S : ConnectionSet 17,
      ∀ H : Subgroup (Equiv.Perm CayleyGroup),
        (∀ p : Equiv.Perm CayleyGroup, p ∈ H → preservesGraph S p) →
        regularOn H →
        Nonempty (H ≃* Multiplicative CayleyGroup) →
        conjugatesToNaturalTranslations S H

def complementSet (S : Finset CayleyGroup) : Finset CayleyGroup :=
  (Finset.univ.erase 0).filter (fun x => x ∉ S)

def complementConnection {k : ℕ} (S : ConnectionSet k) : Finset CayleyGroup :=
  complementSet S.1

def complementPreservesGraph (S T : ConnectionSet 17) : Prop :=
  graphEquivalent S T ↔
    (∃ e : CayleyGroup ≃ CayleyGroup,
      ∀ x y : CayleyGroup,
        cayleyAdj (complementConnection S) x y ↔
          cayleyAdj (complementConnection T) (e x) (e y))

def complementPreservesAutomorphisms (S T : ConnectionSet 17) : Prop :=
  automorphismEquivalent S T ↔
    (∃ e : CayleyGroup ≃+ CayleyGroup,
      (complementConnection S).image e = complementConnection T)

/-- Complementation of valency seventeen and the resulting valency-fifty-four
CI theorem on `C₂³ × C₃²`. -/
def claim37543 : Prop :=
  Fintype.card CayleyGroup = 72 ∧
    (∀ S : ConnectionSet 17,
      (complementConnection S).card = 54 ∧
        (∀ x : CayleyGroup,
          x ∈ complementConnection S ↔
            x ≠ 0 ∧ x ∉ S.1) ∧
        (∀ x : CayleyGroup,
          x ∈ complementConnection S ↔ -x ∈ complementConnection S)) ∧
    (∀ S T : ConnectionSet 17,
      complementPreservesGraph S T ∧ complementPreservesAutomorphisms S T) ∧
    isCI 54

end MathlibPlus.Open.Research.R1468
