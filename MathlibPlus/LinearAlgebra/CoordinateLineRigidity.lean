-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 57136: a bijection of a product of three-element fields which
preserves each coordinate parallel class is coordinatewise, and is linear
after the origin is fixed. -/
theorem coordinate_line_rigidity_claim57136
    (r : ℕ)
    (f : (Fin r → ZMod 3) ≃ (Fin r → ZMod 3))
    (hf0 : f 0 = 0)
    (hparallel :
      ∀ i a b,
        (∀ j, j ≠ i → a j = b j) ↔
          (∀ j, j ≠ i → f a j = f b j)) :
    ∃ σ : Fin r → (ZMod 3 → ZMod 3),
      (∀ i, Function.Bijective (σ i)) ∧
      (∀ i, σ i 0 = 0) ∧
      (∀ a i, f a i = σ i (a i)) ∧
      (∀ i, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
        ∀ x, σ i x = ε * x) ∧
      (∀ a b, f (a + b) = f a + f b) ∧
      (∀ (c : ZMod 3) a, f (c • a) = c • f a) := by
  let axis : Fin r → ZMod 3 → Fin r → ZMod 3 :=
    fun i x j => if i = j then x else 0
  let σ : Fin r → ZMod 3 → ZMod 3 :=
    fun i x => f (axis i x) i
  have haxis (i : Fin r) (x : ZMod 3) : axis i x i = x := by
    simp [axis]
  have haxis_zero (i : Fin r) : axis i 0 = 0 := by
    funext j
    by_cases h : i = j <;> simp [axis, h]
  have hform : ∀ a i, f a i = σ i (a i) := by
    intro a i
    let base : Fin r → ZMod 3 := axis i (a i)
    let g : Finset (Fin r) → Fin r → ZMod 3 :=
      fun s j => if j ∈ s then a j else base j
    have hconst : ∀ s : Finset (Fin r), s ⊆ Finset.univ.erase i →
        f (g s) i = f base i := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro hs
          simpa [g]
      | @insert j s hj ih =>
          intro hs
          have hs' : s ⊆ Finset.univ.erase i := by
            intro k hk
            exact hs (Finset.mem_insert_of_mem hk)
          have hji : j ≠ i := by
            have hjmem : j ∈ Finset.univ.erase i :=
              hs (Finset.mem_insert_self j s)
            exact (Finset.mem_erase.mp hjmem).1
          have hagree : ∀ k, k ≠ j → g (insert j s) k = g s k := by
            intro k hkj
            simp [g, hkj]
          have hout := (hparallel j (g (insert j s)) (g s)).mp hagree
          exact (hout i (Ne.symm hji)).trans (ih hs')
    have hlast := hconst (Finset.univ.erase i) (by simp)
    have hga : g (Finset.univ.erase i) = a := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [g, base, axis]
      · have hjmem : j ∈ Finset.univ.erase i :=
          Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
        simp [g, hjmem]
    rw [hga] at hlast
    simpa [σ, base]
      using hlast
  have hinj (i : Fin r) : Function.Injective (σ i) := by
    intro x y hxy
    have hxy' : f (axis i x) i = f (axis i y) i := by
      simpa [σ] using hxy
    have hagree : ∀ j, j ≠ i → axis i x j = axis i y j := by
      intro j hji
      simp [axis, Ne.symm hji]
    have hout := (hparallel i (axis i x) (axis i y)).mp hagree
    have hfeq : f (axis i x) = f (axis i y) := by
      funext j
      by_cases hji : j = i
      · subst j
        exact hxy'
      · exact hout j hji
    have haxeq := f.injective hfeq
    simpa [axis] using congrFun haxeq i
  have hsurj (i : Fin r) : Function.Surjective (σ i) := by
    intro y
    obtain ⟨a, ha⟩ := f.surjective (axis i y)
    refine ⟨a i, ?_⟩
    calc
      σ i (a i) = f a i := (hform a i).symm
      _ = axis i y i := by rw [ha]
      _ = y := haxis i y
  have hzero (i : Fin r) : σ i 0 = 0 := by
    simp [σ, haxis_zero i, hf0]
  have value_cases : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = -1 := by
    intro z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (by
        change (2 : ZMod 3) = -1
        native_decide))
  have classify :
      ∀ (g : ZMod 3 → ZMod 3), Function.Injective g → g 0 = 0 →
        ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ x, g x = ε * x := by
    intro g hg hg0
    have g1_ne_zero : g 1 ≠ 0 := by
      intro h
      have hbad : g 1 = g 0 := h.trans hg0.symm
      have : (1 : ZMod 3) = 0 := hg hbad
      have hne : (1 : ZMod 3) ≠ 0 := by decide
      exact hne this
    have g1_cases : g 1 = 1 ∨ g 1 = -1 := by
      rcases value_cases (g 1) with h | h | h
      · exact False.elim (g1_ne_zero h)
      · exact Or.inl h
      · exact Or.inr h
    rcases g1_cases with g1 | g1
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro x
      rcases value_cases x with rfl | rfl | rfl
      · simp [hg0]
      · simpa [g1]
      · have gm_ne_zero : g (-1) ≠ 0 := by
          intro h
          have hbad : g (-1) = g 0 := h.trans hg0.symm
          have : (-1 : ZMod 3) = 0 := hg hbad
          have hne : (-1 : ZMod 3) ≠ 0 := by decide
          exact hne this
        have gm_ne_one : g (-1) ≠ 1 := by
          intro h
          have hbad : g (-1) = g 1 := h.trans g1.symm
          have : (-1 : ZMod 3) = 1 := hg hbad
          have hne : (-1 : ZMod 3) ≠ 1 := by decide
          exact hne this
        rcases value_cases (g (-1)) with h | h | h
        · exact False.elim (gm_ne_zero h)
        · exact False.elim (gm_ne_one h)
        · simpa using h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro x
      rcases value_cases x with rfl | rfl | rfl
      · simp [hg0]
      · simpa [g1]
      · have gm_ne_zero : g (-1) ≠ 0 := by
          intro h
          have hbad : g (-1) = g 0 := h.trans hg0.symm
          have : (-1 : ZMod 3) = 0 := hg hbad
          have hne : (-1 : ZMod 3) ≠ 0 := by decide
          exact hne this
        have gm_ne_neg_one : g (-1) ≠ -1 := by
          intro h
          have hbad : g (-1) = g 1 := h.trans g1.symm
          have : (-1 : ZMod 3) = 1 := hg hbad
          have hne : (-1 : ZMod 3) ≠ 1 := by decide
          exact hne this
        rcases value_cases (g (-1)) with h | h | h
        · exact False.elim (gm_ne_zero h)
        · simpa using h
        · exact False.elim (gm_ne_neg_one h)
  have hlinear : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    funext i
    change f (a + b) i = f a i + f b i
    rw [hform (a + b) i, hform a i, hform b i]
    obtain ⟨ε, hε, hσ⟩ := classify (σ i) (hinj i) (hzero i)
    rw [hσ, hσ, hσ, Pi.add_apply]
    rcases hε with rfl | rfl <;> ring
  have hsmul : ∀ (c : ZMod 3) a, f (c • a) = c • f a := by
    intro c a
    rcases value_cases c with rfl | rfl | rfl
    · simp [hf0]
    · simp
    · have hneg : f (-a) = -f a := by
        have h : f (-a) + f a = 0 := by
          simpa [hf0] using (hlinear (-a) a).symm
        exact eq_neg_of_add_eq_zero_left h
      simpa using hneg
  refine ⟨σ, ?_, ?_, hform, ?_, hlinear, hsmul⟩
  · intro i
    exact ⟨hinj i, hsurj i⟩
  · exact hzero
  · intro i
    exact classify (σ i) (hinj i) (hzero i)

end MathlibPlus.LinearAlgebra
