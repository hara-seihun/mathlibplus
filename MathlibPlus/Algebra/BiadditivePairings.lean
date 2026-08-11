import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-! Formalization of admitted claim 12194. -/

/-- An idempotent element is annihilated in either argument of a biadditive pairing. -/
theorem biadditive_idempotent_annihilates
    {M G : Type*} [AddCommMonoid M] [AddCommGroup G]
    (B : M →+ M →+ G) (e : M) (he : e + e = e) :
    ∀ y : M, B e y = 0 ∧ B y e = 0 := by
  intro y
  have hleft : B e y + B e y = B e y := by
    calc
      B e y + B e y = B (e + e) y := by
        rw [map_add, AddMonoidHom.add_apply]
      _ = B e y := by rw [he]
  have hright : B y e + B y e = B y e := by
    calc
      B y e + B y e = B y (e + e) := by
        rw [map_add]
      _ = B y e := by rw [he]
  exact ⟨add_eq_right.mp hleft, add_eq_right.mp hright⟩

end MathlibPlus.Algebra
