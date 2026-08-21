import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ReconstructionFixture

noncomputable section
open Classical

abbrev P4Vertex := Fin 4

def p4Adj (u v : P4Vertex) : Prop :=
  u.val + 1 = v.val ∨ v.val + 1 = u.val

def p4Degree (v : P4Vertex) : ℕ :=
  (Finset.univ.filter (fun u => p4Adj v u)).card

def p4Pi0 : Equiv.Perm P4Vertex := Equiv.swap (1 : P4Vertex) (3 : P4Vertex)

def p4Pi1 : Equiv.Perm P4Vertex := Equiv.swap (2 : P4Vertex) (3 : P4Vertex)

def p4Pi2 : Equiv.Perm P4Vertex := Equiv.swap (0 : P4Vertex) (1 : P4Vertex)

def p4Pi3 : Equiv.Perm P4Vertex := Equiv.swap (0 : P4Vertex) (2 : P4Vertex)

def p4CardIsoFixes (i : P4Vertex) (π : Equiv.Perm P4Vertex) : Prop :=
  π i = i ∧
  ∀ u v : P4Vertex, u ≠ i → v ≠ i →
    (p4Adj u v ↔ p4Adj (π u) (π v))

def p4GlobalIso (π : Equiv.Perm P4Vertex) : Prop :=
  ∀ u v : P4Vertex, p4Adj u v ↔ p4Adj (π u) (π v)

def p4ForwardChanges (i : P4Vertex) (π : Equiv.Perm P4Vertex) : ℕ :=
  (Finset.univ.filter
    (fun u => u ≠ i ∧ ¬ p4Adj i u ∧ p4Adj i (π u))).card

def p4BackwardChanges (i : P4Vertex) (π : Equiv.Perm P4Vertex) : ℕ :=
  (Finset.univ.filter
    (fun u => u ≠ i ∧ p4Adj i u ∧ ¬ p4Adj i (π u))).card

def p4LocalWitness (i : P4Vertex) (π : Equiv.Perm P4Vertex) : Prop :=
  p4CardIsoFixes i π ∧
  ¬ p4GlobalIso π ∧
  p4ForwardChanges i π = 1 ∧
  p4BackwardChanges i π = 1

/-- The four explicit non-global card automorphisms of the path `P₄`, together
with the degree vector and the identity global automorphism. -/
def P4LocalCardWitness : Prop :=
  p4Degree 0 = 1 ∧
  p4Degree 1 = 2 ∧
  p4Degree 2 = 2 ∧
  p4Degree 3 = 1 ∧
  p4LocalWitness 0 p4Pi0 ∧
  p4LocalWitness 1 p4Pi1 ∧
  p4LocalWitness 2 p4Pi2 ∧
  p4LocalWitness 3 p4Pi3 ∧
  p4GlobalIso (Equiv.refl P4Vertex)

end

end MathlibPlus.Open.ResearchFormalization.ReconstructionFixture
