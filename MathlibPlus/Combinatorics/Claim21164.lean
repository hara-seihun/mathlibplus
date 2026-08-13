import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 21164.  The four labels `0,1,2,3` stand for `H₀,H₁,H₂,H₃`.
Assuming that the displayed list is exactly the compatible-pair relation,
three pairwise compatible factors must all have type `H₃`. -/
theorem compatibilityGraph_21164
    (Compatible : Fin 4 → Fin 4 → Prop)
    (hCompatible : ∀ a b, Compatible a b ↔
      (a = 0 ∧ b = 1) ∨
      (a = 1 ∧ b = 0) ∨
      (a = 0 ∧ b = 2) ∨
      (a = 2 ∧ b = 0) ∨
      (a = 3 ∧ b = 3))
    (a b c : Fin 4)
    (hab : Compatible a b)
    (hac : Compatible a c)
    (hbc : Compatible b c) :
    a = 3 ∧ b = 3 ∧ c = 3 := by
  have hab' := (hCompatible a b).1 hab
  have hac' := (hCompatible a c).1 hac
  have hbc' := (hCompatible b c).1 hbc
  rcases hab' with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩ | ⟨ha0, hb2⟩ |
      ⟨ha2, hb0⟩ | ⟨ha3, hb3⟩ <;>
    rcases hac' with ⟨ha0', hc1⟩ | ⟨ha1', hc0⟩ | ⟨ha0', hc2⟩ |
        ⟨ha2', hc0⟩ | ⟨ha3', hc3⟩ <;>
      rcases hbc' with ⟨hb0', hc1'⟩ | ⟨hb1', hc0'⟩ | ⟨hb0', hc2'⟩ |
          ⟨hb2', hc0'⟩ | ⟨hb3', hc3'⟩ <;>
        simp_all

end MathlibPlus.Combinatorics
