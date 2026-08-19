import MathlibPlus.Open.ResearchFormalization.R3630

namespace MathlibPlus.Open.ResearchFormalization.Claim61204

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization

abbrev Cube := RademacherCube 5

/-- The real value of a Boolean sign, with `false` representing `-1`. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Uniform averaging on the five independent sign coordinates. -/
def uniformAverage (f : Cube → ℝ) : ℝ :=
  (∑ x : Cube, f x) / (Fintype.card Cube : ℝ)

def cylinderProbability (S : Finset (Fin 5)) (a : Cube) : ℝ :=
  ((Finset.univ.filter (fun x : Cube => ∀ i ∈ S, x i = a i)).card : ℝ) /
    (Fintype.card Cube : ℝ)

/-- The finite cube carries the independent uniform Rademacher law. -/
def independentUniformSigns : Prop :=
  ∀ (S : Finset (Fin 5)) (a : Cube),
    cylinderProbability S a = (1 / 2 : ℝ) ^ S.card

/-- The four displayed depth-at-most-two Boolean atoms. -/
def h₁ (x : Cube) : ℝ :=
  -signValue (x 0) * signValue (x 1)

def h₂ (x : Cube) : ℝ :=
  (-1 + signValue (x 2) - signValue (x 4) -
      signValue (x 2) * signValue (x 4)) / 2

def h₃ (x : Cube) : ℝ :=
  (signValue (x 2) - signValue (x 4) -
      signValue (x 3) * signValue (x 2) -
      signValue (x 3) * signValue (x 4)) / 2

def h₄ (x : Cube) : ℝ :=
  signValue (x 0)

/-- The explicit legal trees witnessing the depth bound of the four atoms. -/
def treeH₁ : DecisionTree 5 :=
  .query 0
    (.query 1 (.leaf (-1 : ℝ)) (.leaf (1 : ℝ)))
    (.query 1 (.leaf (1 : ℝ)) (.leaf (-1 : ℝ)))

def treeH₂ : DecisionTree 5 :=
  .query 2 (.leaf (-1 : ℝ))
    (.query 4 (.leaf (1 : ℝ)) (.leaf (-1 : ℝ)))

def treeH₃ : DecisionTree 5 :=
  .query 3
    (.query 2 (.leaf (-1 : ℝ)) (.leaf (1 : ℝ)))
    (.query 4 (.leaf (1 : ℝ)) (.leaf (-1 : ℝ)))

def treeH₄ : DecisionTree 5 :=
  .query 0 (.leaf (-1 : ℝ)) (.leaf (1 : ℝ))

def treeDepth : DecisionTree 5 → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      max (treeDepth negative) (treeDepth positive) + 1

def treeNoRepeatFrom (seen : Finset (Fin 5)) : DecisionTree 5 → Prop
  | .leaf _ => True
  | .query coordinate negative positive =>
      coordinate ∉ seen ∧
        treeNoRepeatFrom (insert coordinate seen) negative ∧
          treeNoRepeatFrom (insert coordinate seen) positive

def legalDepthTwoAtom (f : Cube → ℝ) (tree : DecisionTree 5) : Prop :=
  treeDepth tree ≤ 2 ∧
    treeNoRepeatFrom ∅ tree ∧
      (∀ x : Cube, tree.evaluate x = f x) ∧
        (∀ x : Cube, f x = 1 ∨ f x = -1)

/-- The four masses in the admitted law. -/
def atom (k : Fin 4) : Cube → ℝ :=
  if k = 0 then h₁
  else if k = 1 then h₂
  else if k = 2 then h₃
  else h₄

def atomMass (k : Fin 4) : ℝ :=
  if k = 0 then 597 / 1400
  else if k = 1 then 199 / 1400
  else if k = 2 then 597 / 1400
  else 1 / 200

/-- The fixed target is the mixture mean `g = E H`. -/
def target (x : Cube) : ℝ :=
  ∑ k : Fin 4, atomMass k * atom k x

def targetMean : ℝ :=
uniformAverage target

def targetVariance : ℝ :=
uniformAverage (fun x => (target x - targetMean) ^ 2)

def walshCharacter (S : Finset (Fin 5)) (x : Cube) : ℝ :=
  ∏ i ∈ S, signValue (x i)

def walshCoefficient (f : Cube → ℝ) (S : Finset (Fin 5)) : ℝ :=
  uniformAverage (fun x => f x * walshCharacter S x)

def atomFirstCoefficient (f : Cube → ℝ) (i : Fin 5) : ℝ :=
  walshCoefficient f {i}

def atomPairCoefficient (f : Cube → ℝ) (i j : Fin 5) : ℝ :=
  walshCoefficient f {i, j}

def barA (i : Fin 5) : ℝ :=
  ∑ k : Fin 4, atomMass k * atomFirstCoefficient (atom k) i

def barB (i j : Fin 5) : ℝ :=
  ∑ k : Fin 4, atomMass k * atomPairCoefficient (atom k) i j

def walshVariance : ℝ :=
  (∑ i : Fin 5, barA i ^ 2) +
    ∑ i : Fin 5, ∑ j : Fin 5,
      if i < j then barB i j ^ 2 else 0

def atomLoad (f : Cube → ℝ) (i : Fin 5) : ℝ :=
  atomFirstCoefficient f i ^ 2 +
    ∑ j : Fin 5, if j ≠ i then |atomPairCoefficient f i j| else 0

def load (i : Fin 5) : ℝ :=
  ∑ k : Fin 4, atomMass k * atomLoad (atom k) i

/-- The conditional uniform average on a first-reveal branch. -/
def branchCell (i : Fin 5) (b : Bool) : Finset Cube :=
  Finset.univ.filter (fun x : Cube => x i = b)

def branchAverage (i : Fin 5) (b : Bool) (f : Cube → ℝ) : ℝ :=
  (branchCell i b).sum f / ((branchCell i b).card : ℝ)

def branchCoefficient (f : Cube → ℝ) (i : Fin 5) (b : Bool)
    (S : Finset (Fin 5)) : ℝ :=
  branchAverage i b (fun x => f x * walshCharacter S x)

def branchAtomLoad (i : Fin 5) (b : Bool) (f : Cube → ℝ) (j : Fin 5) : ℝ :=
  branchCoefficient f i b {j} ^ 2 +
    ∑ k : Fin 5,
      if k ≠ j ∧ k ≠ i then |branchCoefficient f i b {j, k}| else 0

def branchLoad (i : Fin 5) (b : Bool) (j : Fin 5) : ℝ :=
  ∑ k : Fin 4, atomMass k * branchAtomLoad i b (atom k) j

/-- The maximum conditional intrinsic load over coordinates other than the
revealed coordinate. -/
noncomputable def branchMaximum (i : Fin 5) (b : Bool) : ℝ :=
  sSup {q : ℝ | ∃ j : Fin 5, j ≠ i ∧ q = branchLoad i b j}

def branchVariance (i : Fin 5) (b : Bool) : ℝ :=
  branchAverage i b (fun x => (target x - branchAverage i b target) ^ 2)

def positivePart (r : ℝ) : ℝ :=
  max r 0

def positiveSlackCredit (i : Fin 5) : ℝ :=
  (positivePart (branchMaximum i false - branchVariance i false) +
      positivePart (branchMaximum i true - branchVariance i true)) / 2

def positiveSlackMargin (i : Fin 5) : ℝ :=
  load i + positiveSlackCredit i - targetVariance

def positiveSlackCondition (i : Fin 5) : Prop :=
  targetVariance ≤ load i + positiveSlackCredit i

/-- Root-inclusive Bellman optimum over fresh-coordinate deterministic trees. -/
noncomputable def bellmanOptimalArea : ℝ :=
  R3630.realIntrinsicArea target

/-- Claim 61204: the exact four-atom witness defeats the maximum-load root
selection rule while retaining repairing coordinates and area below two. -/
def claim61204 : Prop :=
  independentUniformSigns ∧
    (∀ x : Cube, h₁ x = 1 ∨ h₁ x = -1) ∧
    (∀ x : Cube, h₂ x = 1 ∨ h₂ x = -1) ∧
    (∀ x : Cube, h₃ x = 1 ∨ h₃ x = -1) ∧
    (∀ x : Cube, h₄ x = 1 ∨ h₄ x = -1) ∧
    (∀ x : Cube,
      h₂ x = if x 2 = false then -1 else -signValue (x 4)) ∧
    (∀ x : Cube,
      h₃ x = if x 3 = false then signValue (x 2) else -signValue (x 4)) ∧
    legalDepthTwoAtom h₁ treeH₁ ∧
    legalDepthTwoAtom h₂ treeH₂ ∧
    legalDepthTwoAtom h₃ treeH₃ ∧
    legalDepthTwoAtom h₄ treeH₄ ∧
    (∀ k : Fin 4, 0 ≤ atomMass k) ∧
    (∑ k : Fin 4, atomMass k) = 1 ∧
    barA 0 = 1 / 200 ∧
    barA 1 = 0 ∧
    barA 2 = 199 / 700 ∧
    barA 3 = 0 ∧
    barA 4 = -(199 : ℝ) / 700 ∧
    (∀ i j : Fin 5, i < j →
      barB i j =
        if i = 0 ∧ j = 1 then -(597 : ℝ) / 1400
        else if i = 2 ∧ j = 4 then -(199 : ℝ) / 2800
        else if i = 2 ∧ j = 3 then -(597 : ℝ) / 2800
        else if i = 3 ∧ j = 4 then -(597 : ℝ) / 2800
        else 0) ∧
    targetVariance = walshVariance ∧
    targetVariance = 3445483 / 7840000 ∧
    load 0 = 151 / 350 ∧
    (∀ i : Fin 5, i ≠ 0 → load i = 597 / 1400) ∧
    (∀ i : Fin 5, i ≠ 0 → load 0 > load i) ∧
    (∀ i : Fin 5, targetVariance > load i) ∧
    branchMaximum 0 false = 597 / 1400 ∧
    branchMaximum 0 true = 597 / 1400 ∧
    branchVariance 0 false = 3445287 / 7840000 ∧
    branchVariance 0 true = 3445287 / 7840000 ∧
    (∀ b : Bool,
      branchMaximum 0 b - branchVariance 0 b = -(102087 : ℝ) / 7840000) ∧
    positivePart (branchMaximum 0 false - branchVariance 0 false) = 0 ∧
    positivePart (branchMaximum 0 true - branchVariance 0 true) = 0 ∧
    positiveSlackMargin 0 = -(63083 : ℝ) / 7840000 ∧
    positiveSlackMargin 0 < 0 ∧
    ¬ positiveSlackCondition 0 ∧
    positiveSlackMargin 2 = 11759 / 156800 ∧
    positiveSlackMargin 3 = 315617 / 3920000 ∧
    positiveSlackMargin 4 = 11759 / 156800 ∧
    positiveSlackCondition 2 ∧
    positiveSlackCondition 3 ∧
    positiveSlackCondition 4 ∧
    bellmanOptimalArea = 35643 / 28000 ∧
    bellmanOptimalArea < 2

end

end MathlibPlus.Open.ResearchFormalization.Claim61204
