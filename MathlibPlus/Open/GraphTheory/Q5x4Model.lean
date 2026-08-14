import Mathlib

namespace MathlibPlus.Open.GraphTheory

abbrev F11Model := ZMod 11

structure Q5x4Model where
  y : ZMod 5
  i : Fin 4
  deriving DecidableEq, Fintype

def q5x4One : Q5x4Model :=
  ⟨0, ⟨0, by omega⟩⟩

def q5x4Mul (a b : Q5x4Model) : Q5x4Model :=
  let even : Prop := a.i.1 % 2 = 0
  let e : ZMod 5 := if even then 1 else -1
  ⟨a.y + e * b.y, ⟨(a.i.1 + b.i.1) % 4, by omega⟩⟩

def q5x4Inv (a : Q5x4Model) : Q5x4Model :=
  let even : Prop := a.i.1 % 2 = 0
  let e : ZMod 5 := if even then 1 else -1
  ⟨-(e * a.y), ⟨(4 - a.i.1) % 4, by omega⟩⟩

def q5x4Chi (q : Q5x4Model) : F11Model :=
  if q.i.1 % 2 = 0 then 1 else -1

abbrev G220Model := F11Model × Q5x4Model

def g220ModelOne : G220Model := (0, q5x4One)

def g220ModelMul (a b : G220Model) : G220Model :=
  (a.1 + q5x4Chi a.2 * b.1, q5x4Mul a.2 b.2)

def g220ModelInv (a : G220Model) : G220Model :=
  (-(q5x4Chi a.2 * a.1), q5x4Inv a.2)

/-- Claim 43663: the displayed `C₅ ⋊ C₄` operation, its sign character,
and the resulting order-220 semidirect product are the fixed model. -/
def fixedSemidirectProductQ220 : Prop :=
  Fintype.card Q5x4Model = 20 ∧ Fintype.card G220Model = 220 ∧
  (∀ a b c : Q5x4Model,
    q5x4Mul (q5x4Mul a b) c = q5x4Mul a (q5x4Mul b c)) ∧
  (∀ a : Q5x4Model,
    q5x4Mul q5x4One a = a ∧ q5x4Mul a q5x4One = a ∧
      q5x4Mul (q5x4Inv a) a = q5x4One ∧
      q5x4Mul a (q5x4Inv a) = q5x4One) ∧
  (∀ a b : Q5x4Model,
    q5x4Chi (q5x4Mul a b) = q5x4Chi a * q5x4Chi b) ∧
  (∀ a b c : G220Model,
    g220ModelMul (g220ModelMul a b) c =
      g220ModelMul a (g220ModelMul b c)) ∧
  (∀ a : G220Model,
    g220ModelMul g220ModelOne a = a ∧
      g220ModelMul a g220ModelOne = a ∧
      g220ModelMul (g220ModelInv a) a = g220ModelOne ∧
      g220ModelMul a (g220ModelInv a) = g220ModelOne) ∧
  (∀ q : Q5x4Model,
    q5x4Chi q = 1 ↔ q.i.1 % 2 = 0)

end MathlibPlus.Open.GraphTheory
