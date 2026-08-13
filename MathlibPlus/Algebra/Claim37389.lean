import Mathlib

namespace MathlibPlus.Algebra.Claim37389

/-- Under the explicit convention `f i = a + b * (-1)^i`, the nonconstant
constant-plus-alternating profiles in `𝔽_q^8` are parametrized by `a` and a
nonzero alternating amplitude `b`. -/
theorem constantPlusAlternatingProfileCard_claim37389
    (q : ℕ) [Fact (Nat.Prime q)] (hq : 2 < q) :
    let encode : ZMod q × {b : ZMod q // b ≠ 0} → (Fin 8 → ZMod q) :=
      fun p i => p.1 + p.2.1 * (-1 : ZMod q) ^ (i : ℕ)
    let profiles : Set (Fin 8 → ZMod q) := Set.range encode
    Fintype.card profiles = q * (q - 1) := by
  let encode : ZMod q × {b : ZMod q // b ≠ 0} → (Fin 8 → ZMod q) :=
    fun p i => p.1 + p.2.1 * (-1 : ZMod q) ^ (i : ℕ)
  let profiles : Set (Fin 8 → ZMod q) := Set.range encode
  have hqprime : Nat.Prime q := Fact.out
  have hq_not_dvd_two : ¬ q ∣ 2 := by
    intro hdiv
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have htwo : (2 : ZMod q) ≠ 0 := by
    change ((2 : ℕ) : ZMod q) ≠ 0
    intro hz
    exact hq_not_dvd_two ((ZMod.natCast_eq_zero_iff 2 q).mp hz)
  have hinj : Function.Injective encode := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h0 := congrFun h ⟨0, by omega⟩
    have h1 := congrFun h ⟨1, by omega⟩
    simp [encode] at h0 h1
    have ha : (2 : ZMod q) * a = 2 * a' := by
      linear_combination h0 + h1
    have hb : (2 : ZMod q) * b.1 = 2 * b'.1 := by
      linear_combination h0 - h1
    have haa : a = a' := mul_left_cancel₀ htwo ha
    have hbb : b.1 = b'.1 := mul_left_cancel₀ htwo hb
    exact Prod.ext haa (Subtype.ext hbb)
  have hzero : Fintype.card {b : ZMod q // b = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, rfl⟩, ?_⟩
    intro b
    apply Subtype.ext
    exact b.property
  have hnonzero : Fintype.card {b : ZMod q // b ≠ 0} = q - 1 := by
    have h := Fintype.card_subtype_compl (α := ZMod q) (fun b => b = 0)
    rw [ZMod.card q, hzero] at h
    simpa only [ne_eq] using h
  have hequiv : (ZMod q × {b : ZMod q // b ≠ 0}) ≃ (Set.range encode) :=
    Equiv.ofInjective encode hinj
  dsimp [profiles]
  calc
    Fintype.card (Set.range encode) =
        Fintype.card (ZMod q × {b : ZMod q // b ≠ 0}) :=
      (Fintype.card_congr hequiv).symm
    _ = Fintype.card (ZMod q) * Fintype.card {b : ZMod q // b ≠ 0} :=
      Fintype.card_prod _ _
    _ = q * (q - 1) := by rw [ZMod.card q, hnonzero]

end MathlibPlus.Algebra.Claim37389
