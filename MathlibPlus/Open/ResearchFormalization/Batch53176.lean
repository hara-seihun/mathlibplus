import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev NineTSevenVertex := ZMod 3 × ZMod 3

def cyclicSet (g : NineTSevenVertex) : Set NineTSevenVertex :=
  {x | ∃ n : ℤ, n • g = x}

def coordinatePairing (x y : NineTSevenVertex) : ZMod 3 :=
  x.1 * y.1 + x.2 * y.2

def annihilator (U : Set NineTSevenVertex) : Set NineTSevenVertex :=
  {x | ∀ y, y ∈ U → coordinatePairing x y = 0}

def dualClass (a : ZMod 3) : Set NineTSevenVertex :=
  {x | ∃ j : ZMod 3, x = (a, j)}

def secondAxis : Set NineTSevenVertex :=
  {x | ∃ i : ZMod 3, x = (i, 0)}

def crosses (C H : Set NineTSevenVertex) : Prop :=
  (C ∩ H).Nonempty ∧ (C \ H).Nonempty

def claim53176 : Prop :=
  let U1 := cyclicSet ((1, 0) : NineTSevenVertex)
  let U2 := cyclicSet ((0, 1) : NineTSevenVertex)
  let U1perp := annihilator U1
  let U2perp := annihilator U2
  let U1perpListed : Set NineTSevenVertex := {(0, 0), (0, 1), (0, 2)}
  let U2perpListed : Set NineTSevenVertex := {(0, 0), (1, 0), (2, 0)}
  let Cplus := dualClass 1
  let Cminus := dualClass 2
  U1perp = U1perpListed ∧
    U1perpListed = dualClass 0 ∧
    U2perp = U2perpListed ∧
    U2perpListed = secondAxis ∧
    crosses Cplus U2perp ∧
    crosses Cminus U2perp ∧
    AddSubgroup.closure (Cplus ∪ Cminus) = ⊤ ∧
    ¬ ∃ H : AddSubgroup NineTSevenVertex,
      H < ⊤ ∧ Cplus ∪ Cminus ⊆ (H : Set NineTSevenVertex)

end MathlibPlus.Open.ResearchFormalizationBatch
