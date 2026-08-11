import Mathlib

namespace MathlibPlus.Algebra.Claim48401

/-- In `𝔽_p` for a prime `p ≠ 3`, the equation `T = -3u` and the
relation `v = 2u` determine a unique pair. -/
theorem uniqueCentralResonancePair (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    ∀ T : ZMod p, ∃! uv : ZMod p × ZMod p,
      T = -3 * uv.1 ∧ uv.2 = 2 * uv.1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 3 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h
    have hpeq : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdiv
    exact hp3 hpeq
  intro T
  refine ⟨(-T / 3, 2 * (-T / 3)), ?_, ?_⟩
  · constructor
    · field_simp [h3]
    · rfl
  · intro uv huv
    have hu : uv.1 = -T / 3 := by
      apply (mul_left_cancel₀ (neg_ne_zero.mpr h3))
      calc
        (-3 : ZMod p) * uv.1 = T := huv.1.symm
        _ = (-3 : ZMod p) * (-T / 3) := by
          field_simp [h3]
    apply Prod.ext hu
    calc
      uv.2 = 2 * uv.1 := huv.2
      _ = 2 * (-T / 3) := by rw [hu]

/-- The final at-most-one conclusion in claim 48401 is stated without
inventing a meaning for the source's undefined `nonfixed` predicate: any
subset of the reflected central-resonance solutions is a subsingleton. -/
theorem atMostOneNonfixedCentralResonancePair
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (T : ZMod p) (nonfixed : (ZMod p × ZMod p) → Prop) :
    ∀ ⦃u v : ZMod p × ZMod p⦄,
      nonfixed u → T = -3 * u.1 → u.2 = 2 * u.1 →
      nonfixed v → T = -3 * v.1 → v.2 = 2 * v.1 → u = v := by
  letI : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 3 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h
    have hpeq : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdiv
    exact hp3 hpeq
  intro u v _ hTu hU _ hTv hV
  have hu : u.1 = v.1 := by
    apply (mul_left_cancel₀ (neg_ne_zero.mpr h3))
    exact hTu.symm.trans hTv
  apply Prod.ext hu
  calc
    u.2 = 2 * u.1 := hU
    _ = 2 * v.1 := by rw [hu]
    _ = v.2 := hV.symm

end MathlibPlus.Algebra.Claim48401
