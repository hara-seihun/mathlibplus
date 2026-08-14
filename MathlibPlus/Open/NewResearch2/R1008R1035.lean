import Mathlib

namespace MathlibPlus.Open.NewResearch2.R1008R1035

noncomputable section

abbrev V := Fin 3 → ZMod 2
abbrev LinearMapGroup := V ≃ₗ[ZMod 2] V
abbrev ZeroFixingPermutation := {p : Equiv.Perm V // p 0 = 0}

def linearPermutation (g : LinearMapGroup) : ZeroFixingPermutation :=
  ⟨g.toEquiv, by simp⟩

def isLinear (p : ZeroFixingPermutation) : Prop :=
  ∃ g : LinearMapGroup, linearPermutation g = p

/-- The relation of lying in the same left/right `GL(3,2)` double coset. -/
def sameDoubleCoset (p q : ZeroFixingPermutation) : Prop :=
  ∃ g h : LinearMapGroup,
    (linearPermutation g).1 * p.1 * (linearPermutation h).1 = q.1

/-- Claim 28196: the zero-fixing permutations of `C₂³` split into four
left/right linear double cosets, one linear and three nonlinear. -/
def claim28196 : Prop :=
  ∃ (Q : ZeroFixingPermutation → Fin 4),
    (∀ p q, Q p = Q q ↔ sameDoubleCoset p q) ∧
    (∃ p₀, isLinear p₀ ∧ ∀ p, Q p = Q p₀ ↔ isLinear p) ∧
    (∃ p₀ p₁ p₂ p₃,
      isLinear p₀ ∧ ¬ isLinear p₁ ∧ ¬ isLinear p₂ ∧ ¬ isLinear p₃ ∧
      Q p₁ ≠ Q p₂ ∧ Q p₁ ≠ Q p₃ ∧ Q p₂ ≠ Q p₃ ∧
      ∀ p, Q p = Q p₀ ∨ Q p = Q p₁ ∨ Q p = Q p₂ ∨ Q p = Q p₃)

end

end MathlibPlus.Open.NewResearch2.R1008R1035
