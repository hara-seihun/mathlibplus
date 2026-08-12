import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.OrientationCode

/-- Claim 35697: an orientation code acts by a sign on the `C₃` phase
coordinate. The source packet leaves the ambient group-coordinate types
implicit, so `N` and `B` are retained as abstract block coordinates. -/
theorem orientationCode_properties
    {N B : Type*} (ε : B → ZMod 3)
    (hε : ∀ b, ε b = 1 ∨ ε b = -1) :
    let F : N × B × ZMod 3 → N × B × ZMod 3 :=
      fun p => (p.1, p.2.1, ε p.2.1 * p.2.2)
    (∀ p, F (F p) = p) ∧
      (∀ p, (F p).1 = p.1 ∧ (F p).2.1 = p.2.1) ∧
      (∀ n b, F (n, b, 0) = (n, b, 0)) ∧
      (∀ n b, ε b = -1 →
        F (n, b, 1) = (n, b, -1) ∧ F (n, b, -1) = (n, b, 1)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    rcases p with ⟨n, b, i⟩
    rcases hε b with h | h <;> simp [h]
  · intro p
    simp
  · intro n b
    simp
  · intro n b h
    simp [h]

end MathlibPlus.GroupTheory.OrientationCode
