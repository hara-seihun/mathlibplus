import Mathlib

namespace MathlibPlus.GroupTheory

/-! Formalization of admitted claim 38702.  A six-point action is represented by
an action on `Fin 6`; the proof uses the orbit map of one point and retains the
exact order-nine hypothesis. -/

/-- A group of order nine acting on six points has a nonidentity element with a
fixed point. -/
theorem order_nine_action_has_fixed_point
    {G : Type*} [Group G] [Fintype G] [MulAction G (Fin 6)]
    (hcard : Fintype.card G = 9) :
    ∃ g : G, g ≠ 1 ∧ ∃ x : Fin 6, g • x = x := by
  by_contra h
  push Not at h
  let f : G → Fin 6 := fun g => g • (0 : Fin 6)
  have hinj : Function.Injective f := by
    intro g k hfk
    have hfk' : g • (0 : Fin 6) = k • (0 : Fin 6) := by
      simpa [f] using hfk
    by_contra hne
    have hkg_ne : k⁻¹ * g ≠ 1 := by
      intro hkg
      apply hne
      calc
        g = 1 * g := by simp
        _ = k * (k⁻¹ * g) := by simp
        _ = k * 1 := by rw [hkg]
        _ = k := by simp
    have hfix : (k⁻¹ * g) • (0 : Fin 6) = 0 := by
      calc
        (k⁻¹ * g) • (0 : Fin 6) = k⁻¹ • (g • (0 : Fin 6)) := by rw [mul_smul]
        _ = k⁻¹ • (k • (0 : Fin 6)) := by rw [hfk']
        _ = 0 := by simp
    exact (h (k⁻¹ * g) hkg_ne (0 : Fin 6)) hfix
  have hle : Fintype.card G ≤ Fintype.card (Fin 6) :=
    Fintype.card_le_of_injective f hinj
  rw [hcard, Fintype.card_fin] at hle
  omega

end MathlibPlus.GroupTheory
