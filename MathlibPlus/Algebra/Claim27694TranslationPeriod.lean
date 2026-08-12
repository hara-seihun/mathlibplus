import MathlibPlus.Algebra.TranslationPeriod

namespace MathlibPlus.Algebra.TranslationPeriod

noncomputable section

variable {B : Type*} [AddCommGroup B]

/-- Claim 27694.  A bijection that preserves the translation labels of a set
can differ from translation by its value at zero only by a period of the set.
The claim's notation does not impose finiteness, and the proof uses none. -/
theorem translationPeriod_of_map_translate_claim27694
    (X : Set B) (φ : B ≃ B)
    (hφ : ∀ z : B,
      φ '' translateSet X z = translateSet (φ '' X) z) :
    (∀ a : B, translateSet X (φ a - a - φ 0) = X) ∧
      φ '' X = translateSet X (φ 0) := by
  have hpoint (a z : B) :
      a ∈ translateSet X z ↔ φ a ∈ translateSet (φ '' X) z := by
    rw [← hφ z]
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨w, hw, hwa⟩
      have hwa' : w = a := φ.injective hwa
      simpa [hwa'] using hw
  have himage (a : B) :
      φ '' X = translateSet X (φ a - a) := by
    ext y
    constructor
    · intro hy
      have hy_sig :
          φ a ∈ translateSet (φ '' X) (φ a - y) := by
        exact ⟨y, hy, by abel⟩
      have hx_sig : a ∈ translateSet X (φ a - y) :=
        (hpoint a (φ a - y)).mpr hy_sig
      rcases hx_sig with ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      change x + (φ a - y) = a at hxy
      change x + (φ a - a) = y
      calc
        x + (φ a - a) = (x + (φ a - y)) + (y - a) := by abel
        _ = a + (y - a) := by rw [hxy]
        _ = y := by abel
    · intro hy
      rcases hy with ⟨x, hx, hxy⟩
      change x + (φ a - a) = y at hxy
      have hx_sig : a ∈ translateSet X (φ a - y) := by
        refine ⟨x, hx, ?_⟩
        change x + (φ a - y) = a
        calc
          x + (φ a - y) = (x + (φ a - a)) + (a - y) := by abel
          _ = y + (a - y) := by rw [hxy]
          _ = a := by abel
      have hy_sig : φ a ∈ translateSet (φ '' X) (φ a - y) :=
        (hpoint a (φ a - y)).mp hx_sig
      rcases hy_sig with ⟨w, hw, hwy⟩
      have hwy' : w = y := by
        change w + (φ a - y) = φ a at hwy
        apply add_right_cancel (b := φ a - y)
        calc
          w + (φ a - y) = φ a := hwy
          _ = y + (φ a - y) := by abel
      simpa [hwy'] using hw
  constructor
  · intro a
    have htrans :
        translateSet X (φ a - a) = translateSet X (φ 0) := by
      calc
        translateSet X (φ a - a) = φ '' X := (himage a).symm
        _ = translateSet X (φ 0) := by simpa only [sub_zero] using himage 0
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      change x + (φ a - a - φ 0) = y at hxy
      have hyc : y + φ 0 ∈ translateSet X (φ a - a) := by
        refine ⟨x, hx, ?_⟩
        change x + (φ a - a) = y + φ 0
        calc
          x + (φ a - a) = (x + (φ a - a - φ 0)) + φ 0 := by abel
          _ = y + φ 0 := by rw [hxy]
      have hyc' : y + φ 0 ∈ translateSet X (φ 0) := by
        rw [← htrans]
        exact hyc
      rcases hyc' with ⟨w, hw, hwy⟩
      change w + φ 0 = y + φ 0 at hwy
      have hwy' : w = y := by
        exact add_right_cancel hwy
      simpa [hwy'] using hw
    · intro hy
      have hyc : y + φ 0 ∈ translateSet X (φ 0) := ⟨y, hy, rfl⟩
      have hyc' : y + φ 0 ∈ translateSet X (φ a - a) := by
        rw [htrans]
        exact hyc
      rcases hyc' with ⟨w, hw, hwy⟩
      refine ⟨w, hw, ?_⟩
      change w + (φ a - a - φ 0) = y
      change w + (φ a - a) = y + φ 0 at hwy
      calc
        w + (φ a - a - φ 0) = (w + (φ a - a)) - φ 0 := by abel
        _ = (y + φ 0) - φ 0 := by rw [hwy]
        _ = y := by abel
  · simpa only [sub_zero] using himage 0

end
end MathlibPlus.Algebra.TranslationPeriod
