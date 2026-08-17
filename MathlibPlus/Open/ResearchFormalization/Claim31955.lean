import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim31955

abbrev Q12 := ZMod 3 × ZMod 4
abbrev RecognitionVertex := ZMod 13 × Q12

def q12Chi3 (i : ZMod 4) : ZMod 3 :=
  if i = 0 ∨ i = 2 then 1 else -1

def q12Chi13 (h : Q12) : ZMod 13 :=
  if h.2 = 0 ∨ h.2 = 2 then 1 else -1

def q12Mul (x y : Q12) : Q12 :=
  (x.1 + q12Chi3 x.2 * y.1, x.2 + y.2)

def q12U : Set Q12 :=
  {u | u.1 = 1 ∨ u.1 = 2}

def q12Adj (x y : Q12) : Prop :=
  x ≠ y ∧ ∃ u, u ∈ q12U ∧ y = q12Mul x u

def quotientGraph : SimpleGraph Q12 :=
  SimpleGraph.fromRel q12Adj

def q12SwitchCycle (a b c : Q12) : Equiv.Perm Q12 :=
  (Equiv.swap b c).trans (Equiv.swap a b)

def q12Sigma : Equiv.Perm Q12 :=
  (q12SwitchCycle (1, 1) (1, 3) (2, 2)).trans
    (q12SwitchCycle (2, 1) (1, 2) (2, 3))

def q12SigmaInv : Equiv.Perm Q12 :=
  q12Sigma.symm

def recognitionMul (x y : RecognitionVertex) : RecognitionVertex :=
  (x.1 + q12Chi13 x.2 * y.1, q12Mul x.2 y.2)

def recognitionConnection (s : RecognitionVertex) : Prop :=
  s.1 = 0 ∧ s.2 ∈ q12U

def recognitionAdj (x y : RecognitionVertex) : Prop :=
  x ≠ y ∧
    ∃ s, recognitionConnection s ∧ y = recognitionMul x s

def recognitionGraph : SimpleGraph RecognitionVertex :=
  SimpleGraph.fromRel recognitionAdj

def graphAutomorphism {V : Type*} (G : SimpleGraph V) (f : V → V) : Prop :=
  Function.Bijective f ∧ ∀ x y, G.Adj x y ↔ G.Adj (f x) (f y)

def componentLocalSwitch (x : RecognitionVertex) : RecognitionVertex :=
  if x.1 = 0 then (0, q12Sigma x.2) else x

def commonC13Block (v : Q12) : Set RecognitionVertex :=
  {x | x.2 = v}

def commonC13Partition : Set (Set RecognitionVertex) :=
  Set.range commonC13Block

def breaksCommonC13Partition (f : RecognitionVertex → RecognitionVertex) : Prop :=
  ∃ v v₁ v₂ : Q12,
    v₁ ≠ v₂ ∧
      (∃ x, x ∈ f '' commonC13Block v ∧ x.2 = v₁) ∧
      (∃ x, x ∈ f '' commonC13Block v ∧ x.2 = v₂) ∧
      f '' commonC13Block v ∉ commonC13Partition

/-- Claim 31955: the order-three quotient switch used in the zero component is a
full recognition-graph automorphism, but it breaks the common `C₁₃` blocks. -/
def fullGraphAutomorphismBreakingCommonC13Partition : Prop :=
  orderOf q12Sigma = 3 ∧
    graphAutomorphism quotientGraph (fun h => q12Sigma h) ∧
      graphAutomorphism recognitionGraph componentLocalSwitch ∧
        breaksCommonC13Partition componentLocalSwitch

end MathlibPlus.Open.ResearchFormalization.Claim31955
