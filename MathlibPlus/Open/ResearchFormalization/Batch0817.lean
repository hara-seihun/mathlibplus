import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch0817

noncomputable section

abbrev Poly4 := MvPolynomial (Fin 4) ℚ

def labelA : Poly4 := MvPolynomial.X 0
def labelB : Poly4 := MvPolynomial.X 1
def labelC : Poly4 := MvPolynomial.X 2
def labelD : Poly4 := MvPolynomial.X 3

def elementaryTwo (x y z : Poly4) : Poly4 := x * y + x * z + y * z

def elementaryThree (x y z : Poly4) : Poly4 := x * y * z

def stateSigma (x y z u v w : Poly4) : Poly4 × Poly4 :=
  (elementaryTwo x y z + elementaryTwo u v w,
    elementaryThree x y z + elementaryThree u v w)

def stateB : Poly4 × Poly4 :=
  stateSigma labelA labelA labelB labelA labelC labelD

def stateC : Poly4 × Poly4 :=
  stateSigma labelA labelA labelC labelA labelB labelD

def stateD : Poly4 × Poly4 :=
  stateSigma labelA labelA labelD labelA labelB labelC

def chord (p q : Poly4 × Poly4) : Poly4 × Poly4 :=
  (p.1 - q.1, p.2 - q.2)

def directionMinusOneA (s : Poly4) : Poly4 × Poly4 :=
  (s * (-1 : Poly4), s * (-labelA))

/-- Exact universal factorisations for the three states in pattern `a³bcd`. -/
def claim_25025 : Prop :=
  chord stateC stateB =
      directionMinusOneA ((labelA - labelD) * (labelB - labelC)) ∧
    chord stateD stateB =
      directionMinusOneA ((labelA - labelC) * (labelB - labelD)) ∧
    chord stateD stateC =
      directionMinusOneA ((labelA - labelB) * (labelC - labelD))

end

noncomputable section

abbrev Poly5 := MvPolynomial (Fin 5) ℚ

def labelA5 : Poly5 := MvPolynomial.X 0
def labelB5 : Poly5 := MvPolynomial.X 1
def labelC5 : Poly5 := MvPolynomial.X 2
def labelD5 : Poly5 := MvPolynomial.X 3
def labelE5 : Poly5 := MvPolynomial.X 4

def elementaryTwo5 (x y z : Poly5) : Poly5 := x * y + x * z + y * z

def elementaryThree5 (x y z : Poly5) : Poly5 := x * y * z

def stateSigma5 (x y z u v w : Poly5) : Poly5 × Poly5 :=
  (elementaryTwo5 x y z + elementaryTwo5 u v w,
    elementaryThree5 x y z + elementaryThree5 u v w)

def stateBothB : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelA5 labelB5 labelC5 labelD5 labelE5

def stateBothC : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelA5 labelC5 labelB5 labelD5 labelE5

def stateBothD : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelA5 labelD5 labelB5 labelC5 labelE5

def stateBothE : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelA5 labelE5 labelB5 labelC5 labelD5

def stateBC : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelB5 labelC5 labelA5 labelD5 labelE5

def stateBD : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelB5 labelD5 labelA5 labelC5 labelE5

def stateBE : Poly5 × Poly5 :=
  stateSigma5 labelA5 labelB5 labelE5 labelA5 labelC5 labelD5

def chord5 (p q : Poly5 × Poly5) : Poly5 × Poly5 :=
  (p.1 - q.1, p.2 - q.2)

def directionMinusOneA5 (s : Poly5) : Poly5 × Poly5 :=
  (s * (-1 : Poly5), s * (-labelA5))

def hasPrimitiveDirectionMinusOneA5 (p : Poly5 × Poly5) : Prop :=
  ∃ s : Poly5, s ≠ 0 ∧ p = directionMinusOneA5 s

def otherChordsA2BCDE : List (Poly5 × Poly5) :=
  [ chord5 stateBothB stateBothC,
    chord5 stateBothB stateBothD,
    chord5 stateBothB stateBothE,
    chord5 stateBothC stateBothD,
    chord5 stateBothC stateBothE,
    chord5 stateBothD stateBothE,
    chord5 stateBothB stateBC,
    chord5 stateBothB stateBD,
    chord5 stateBothB stateBE,
    chord5 stateBothC stateBC,
    chord5 stateBothC stateBD,
    chord5 stateBothC stateBE,
    chord5 stateBothD stateBC,
    chord5 stateBothD stateBD,
    chord5 stateBothD stateBE,
    chord5 stateBothE stateBC,
    chord5 stateBothE stateBD,
    chord5 stateBothE stateBE ]

/-- The three and only three direction `(-1,-a)` chords in pattern `a²bcde`, with their contents. -/
def claim_25027 : Prop :=
  (∀ p ∈ otherChordsA2BCDE, ¬ hasPrimitiveDirectionMinusOneA5 p) ∧
    hasPrimitiveDirectionMinusOneA5 (chord5 stateBD stateBC) ∧
    hasPrimitiveDirectionMinusOneA5 (chord5 stateBE stateBC) ∧
    hasPrimitiveDirectionMinusOneA5 (chord5 stateBE stateBD) ∧
    chord5 stateBD stateBC =
      directionMinusOneA5 ((labelB5 - labelE5) * (labelC5 - labelD5)) ∧
    chord5 stateBE stateBC =
      directionMinusOneA5 ((labelB5 - labelD5) * (labelC5 - labelE5)) ∧
    chord5 stateBE stateBD =
      directionMinusOneA5 ((labelB5 - labelC5) * (labelD5 - labelE5))

end

end MathlibPlus.Open.ResearchFormalization.Batch0817
