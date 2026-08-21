-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Open.Combinatorics.InversePairCayleyCount

namespace MathlibPlus.Combinatorics

/-- In `C₇²`, inverse-closed identity-free connection sets are freely chosen
from the 24 nonzero inverse pairs. -/
theorem inversePairCayleyConnectionSetCount :
    MathlibPlus.Open.Combinatorics.inversePairCayleyConnectionSetCount := by
  let G := ZMod 7 × ZMod 7
  let code : G → ℕ := fun x => x.1.val * 7 + x.2.val
  let P := {x : G // x ≠ 0 ∧ code x < code (-x)}
  let C := {S : Finset G //
    0 ∉ S ∧ ∀ x : G, x ∈ S → -x ∈ S}
  have hcode : ∀ x : G, x ≠ 0 → code x ≠ code (-x) := by
    native_decide
  let e : Finset P ≃ C :=
    { toFun := fun R =>
        ⟨Finset.univ.filter (fun x : G => ∃ y ∈ R, x = y.1 ∨ x = -y.1), by
          constructor
          · intro h0
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0
            obtain ⟨y, _hy, h | h⟩ := h0
            · exact y.2.1 h.symm
            · exact y.2.1 (neg_eq_zero.mp h.symm)
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            obtain ⟨y, hy, rfl | rfl⟩ := hx
            · exact ⟨y, hy, Or.inr rfl⟩
            · exact ⟨y, hy, Or.inl (neg_neg y.1)⟩⟩
      invFun := fun S => Finset.univ.filter (fun y : P => y.1 ∈ S.1)
      left_inv := by
        intro R
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨z, hz, h | h⟩
          · have hyz : y = z := Subtype.ext h
            simpa only [hyz] using hz
          · exfalso
            have hylt : code y.1 < code (-y.1) := y.2.2
            have hzlt : code z.1 < code (-z.1) := z.2.2
            rw [h] at hylt
            rw [neg_neg] at hylt
            exact (lt_asymm hylt hzlt)
        · intro hy
          exact ⟨y, hy, Or.inl rfl⟩
      right_inv := by
        intro S
        apply Subtype.ext
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨y, hy, rfl | rfl⟩
          · exact hy
          · exact S.2.2 y.1 hy
        · intro hx
          have hx0 : x ≠ 0 := fun h => S.2.1 (h ▸ hx)
          rcases lt_or_gt_of_ne (hcode x hx0) with hlt | hgt
          · exact ⟨⟨x, hx0, hlt⟩, hx, Or.inl rfl⟩
          · have hneg0 : -x ≠ 0 := neg_ne_zero.mpr hx0
            have hnegmem : -x ∈ S.1 := S.2.2 x hx
            exact ⟨⟨-x, hneg0, by rw [neg_neg]; exact hgt⟩,
              hnegmem, Or.inr (neg_neg x).symm⟩ }
  change Fintype.card {x : G // x ≠ 0} = 48 ∧ Fintype.card C = 2 ^ 24
  constructor
  · native_decide
  · have hP : Fintype.card P = 24 := by native_decide
    calc
      Fintype.card C = Fintype.card (Finset P) := Fintype.card_congr e.symm
      _ = 2 ^ Fintype.card P := Fintype.card_finset
      _ = 2 ^ 24 := by rw [hP]

end MathlibPlus.Combinatorics
