import Mathlib

namespace MathlibPlus.Open.Frontier

abbrev Four := Fin 4

def rankThreeTypeBBar : Four → Four := ![3, 2, 1, 0]

def rankThreeLowBitFlip : Four → Four := ![1, 0, 3, 2]

def rankThreeHighBitFlip : Four → Four := ![2, 3, 0, 1]

def rankThreeNegativeMass : Four → ℚ := ![4, 6, 4, 11]

def rankThreePositiveCapacity : Four → ℚ := ![4, 13, 8, 5]

def rankThreeWitness : Four → Four → ℚ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 7 / 11, 4 / 11, 0]]

def rankThreeReflectionEdge (i j : Four) : Prop :=
  j ≠ rankThreeTypeBBar i

def rankThreeColumnLoad (transport : Four → Four → ℚ) (j : Four) : ℚ :=
  ∑ i : Four, rankThreeNegativeMass i * transport i j

def rankThreeRowStochastic (transport : Four → Four → ℚ) : Prop :=
  ∀ i : Four, (∀ j : Four, 0 ≤ transport i j) ∧ ∑ j : Four, transport i j = 1

def rankThreeReflectionSupported (transport : Four → Four → ℚ) : Prop :=
  ∀ i j : Four, ¬ rankThreeReflectionEdge i j → transport i j = 0

def rankThreeRespectsCapacities (transport : Four → Four → ℚ) : Prop :=
  ∀ j : Four, rankThreeColumnLoad transport j ≤ rankThreePositiveCapacity j

def rankThreeHasStrictCapacity (transport : Four → Four → ℚ) : Prop :=
  ∃ j : Four, rankThreeColumnLoad transport j < rankThreePositiveCapacity j

def rankThreeGlobalMixture (lambdaZero lambdaOne lambdaTwo : ℚ) : Four → Four → ℚ :=
  fun i j =>
    if j = i then lambdaZero
    else if j = rankThreeLowBitFlip i then lambdaOne
    else if j = rankThreeHighBitFlip i then lambdaTwo
    else 0

def rankThreeNoFeasibleGlobalMixture : Prop :=
  ¬ ∃ (lambdaZero lambdaOne lambdaTwo : ℚ),
    0 ≤ lambdaZero ∧
    0 ≤ lambdaOne ∧
    0 ≤ lambdaTwo ∧
    lambdaZero + lambdaOne + lambdaTwo = 1 ∧
    rankThreeRespectsCapacities
      (rankThreeGlobalMixture lambdaZero lambdaOne lambdaTwo)

def rankThreeGlobalMixtureObstruction : Prop :=
  (∀ i : Four, 0 < rankThreeNegativeMass i) ∧
  (∀ j : Four, 0 < rankThreePositiveCapacity j) ∧
  rankThreeRowStochastic rankThreeWitness ∧
  rankThreeReflectionSupported rankThreeWitness ∧
  rankThreeRespectsCapacities rankThreeWitness ∧
  rankThreeHasStrictCapacity rankThreeWitness ∧
  rankThreeNoFeasibleGlobalMixture

inductive ParabolicSign
  | positive
  | negative
  deriving DecidableEq

def parabolicSignMul : ParabolicSign → ParabolicSign → ParabolicSign
  | .positive, b => b
  | .negative, .positive => .negative
  | .negative, .negative => .positive

def parabolicSignValue (p : ℕ) : ParabolicSign → ZMod p
  | .positive => 1
  | .negative => -1

abbrev ParabolicH (p : ℕ) := ParabolicSign × (ZMod p × ZMod p)

def parabolicMul (p : ℕ) (g h : ParabolicH p) : ParabolicH p :=
  (parabolicSignMul g.1 h.1,
    (g.2.1 + parabolicSignValue p g.1 * h.2.1,
      g.2.2 + parabolicSignValue p g.1 * h.2.2))

def parabolicPhi (p : ℕ) (g : ParabolicH p) : ParabolicH p :=
  (g.1,
    (g.2.1 - (1 - parabolicSignValue p g.1) * (2 : ZMod p)⁻¹,
      g.2.2))

def parabolicC (p : ℕ) (t : ZMod p) : Set (ParabolicH p) :=
  {g | g.1 = .positive ∧ ∃ z : ZMod p, g.2 = (z, t)}

def parabolicP (p : ℕ) (t : ZMod p) : Set (ParabolicH p) :=
  {g | g.1 = .negative ∧ ∃ z : ZMod p, g.2 = (t + z ^ 2, 2 * z)}

def parabolicT (p : ℕ) : Set (ParabolicH p) :=
  parabolicP p 0 ∪ parabolicP p 1 ∪ parabolicP p 3 ∪
    parabolicC p 1 ∪ parabolicC p (-1)

def parabolicTPrime (p : ℕ) : Set (ParabolicH p) :=
  parabolicP p 0 ∪ parabolicP p (-1) ∪ parabolicP p (-3) ∪
    parabolicC p 1 ∪ parabolicC p (-1)

def parabolicGroupAutomorphism (p : ℕ) : Prop :=
  Function.Bijective (parabolicPhi p) ∧
    ∀ g h : ParabolicH p,
      parabolicPhi p (parabolicMul p g h) =
        parabolicMul p (parabolicPhi p g) (parabolicPhi p h)

def smallPrimeParabolicTranslationObstruction : Prop :=
  ∀ p : ℕ, (p = 3 ∨ p = 5) →
    parabolicGroupAutomorphism p ∧
      Set.image (parabolicPhi p) (parabolicT p) = parabolicTPrime p

end MathlibPlus.Open.Frontier
