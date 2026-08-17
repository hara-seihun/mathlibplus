import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.Open.ResearchFormalization.R1414Claim36928

noncomputable section

abbrev Binary3 := Fin 3 → ZMod 2
abbrev GroupN (n : ℕ) := Binary3 × ZMod n

def binaryBasis (j : Fin 3) : Binary3 :=
  fun i => if i = j then 1 else 0

def e1 : Binary3 := binaryBasis 0
def e2 : Binary3 := binaryBasis 1
def e3 : Binary3 := binaryBasis 2

/-- The exact odd cyclic connection set. -/
def connectionSet (n : ℕ) : Set (GroupN n) :=
  {g | (g.1 = e1 ∧ g.2 ≠ 0) ∨
    (g.1 = e2 ∧ g.2 ≠ 0) ∨
    (g.1 = e3 ∧ g.2 = 0)}

/-- Claim 36928: the displayed odd cyclic connection set is inverse closed,
generates the exact product group, and has the stated cyclic-generator and
binary-basis recovery data. -/
def claim36928 : Prop :=
  ∀ (n : ℕ), 3 ≤ n → Odd n →
    (∀ g : GroupN n, g ∈ connectionSet n → -g ∈ connectionSet n) ∧
      AddSubgroup.closure (connectionSet n) = ⊤ ∧
      ((e1, (2 : ZMod n)) - (e1, (1 : ZMod n)) =
        ((0 : Binary3), (1 : ZMod n))) ∧
      ((0 : Binary3), (1 : ZMod n)) ∈
        AddSubgroup.closure (connectionSet n) ∧
      (e1, (1 : ZMod n)) ∈ connectionSet n ∧
      (e1, (2 : ZMod n)) ∈ connectionSet n ∧
      (e3, (0 : ZMod n)) ∈ connectionSet n ∧
      (e1, (0 : ZMod n)) ∈ AddSubgroup.closure (connectionSet n) ∧
      (e2, (0 : ZMod n)) ∈ AddSubgroup.closure (connectionSet n) ∧
      (e3, (0 : ZMod n)) ∈ AddSubgroup.closure (connectionSet n)

end

end MathlibPlus.Open.ResearchFormalization.R1414Claim36928
