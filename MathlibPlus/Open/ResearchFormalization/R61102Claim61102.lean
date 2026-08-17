import MathlibPlus.Open.ResearchFormalization.RademacherAndTrees
import MathlibPlus.Open.ResearchFormalization.RademacherArea

namespace MathlibPlus.Open.ResearchFormalization.R61102Claim61102

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

abbrev Oracle := Fin 3 → Bool
abbrev History := Fin 3 → Option Bool

/-- The Rademacher sign convention on the Boolean cube. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The three exact Boolean component functions. -/
def T₁ (ω : Oracle) : Bool :=
  if ω 2 then !ω 0 else !ω 1

def T₂ (ω : Oracle) : Bool :=
  if ω 1 then !ω 0 else !ω 2

def T₃ (ω : Oracle) : Bool :=
  if ω 1 = ω 2 then true else false

def componentBoolean : Fin 3 → Oracle → Bool :=
  ![T₁, T₂, T₃]

def componentValue (i : Fin 3) (ω : Oracle) : ℝ :=
  signValue (componentBoolean i ω)

/-- The equal-mixture target. -/
def mixtureTarget (ω : Oracle) : ℝ :=
  (∑ i : Fin 3, componentValue i ω) / 3

/-- Deterministic decision-tree depth, with leaves at depth zero. -/
def treeDepth : DecisionTree 3 → ℕ
  | .leaf _ => 0
  | .query _ ifFalse ifTrue =>
      1 + max (treeDepth ifFalse) (treeDepth ifTrue)

def determinesReal (f : Oracle → ℝ) (tree : DecisionTree 3) : Prop :=
  ∀ ω : Oracle, tree.evaluate ω = f ω

def minimumDeterministicDepth (f : Oracle → ℝ) (d : ℕ) : Prop :=
  (∃ tree : DecisionTree 3,
    noRepeat tree ∧ determinesReal f tree ∧ treeDepth tree = d) ∧
    (∀ tree : DecisionTree 3,
      noRepeat tree → determinesReal f tree → d ≤ treeDepth tree)

/-- Walsh characters and their normalized coefficients on the uniform cube. -/
def uniformAverage (f : Oracle → ℝ) : ℝ :=
  (∑ ω : Oracle, f ω) / (2 : ℝ) ^ 3

def walshCharacter (S : Finset (Fin 3)) (ω : Oracle) : ℝ :=
  S.prod (fun i => signValue (ω i))

def walshCoefficient (f : Oracle → ℝ) (S : Finset (Fin 3)) : ℝ :=
  uniformAverage (fun ω => f ω * walshCharacter S ω)

def nonconstantWalshMass (f : Oracle → ℝ) : ℝ :=
  ∑ S ∈ ((Finset.univ : Finset (Fin 3)).powerset).filter
      (fun S => S.Nonempty),
    |walshCoefficient f S|

/-- A legal adaptive policy reveals an unrevealed coordinate, or stops. -/
structure CoordinatePolicy where
  next : History → Option (Fin 3)

def legalPolicy (p : CoordinatePolicy) : Prop :=
  ∀ (h : History) (c : Fin 3),
    p.next h = some c → h c = none

def emptyHistory : History :=
  fun _ => none

def reveal (h : History) (c : Fin 3) (ω : Oracle) : History :=
  Function.update h c (some (ω c))

def transcript (p : CoordinatePolicy) (ω : Oracle) : ℕ → History
  | 0 => emptyHistory
  | m + 1 =>
      let h := transcript p ω m
      match p.next h with
      | none => h
      | some c => reveal h c ω

def consistent (h : History) (ω : Oracle) : Prop :=
  ∀ (c : Fin 3) (b : Bool), h c = some b → ω c = b

noncomputable def fiber (h : History) : Finset Oracle :=
  Finset.univ.filter (fun ω => consistent h ω)

noncomputable def posteriorVariance (f : Oracle → ℝ) (h : History) : ℝ :=
  let S := fiber h
  if S.Nonempty then
    let n : ℝ := S.card
    (∑ ω ∈ S, (f ω) ^ 2) / n - ((∑ ω ∈ S, f ω) / n) ^ 2
  else
    0

noncomputable def expectedPosteriorVariance
    (f : Oracle → ℝ) (h : Oracle → History) : ℝ :=
  (∑ ω : Oracle, posteriorVariance f (h ω)) / (Fintype.card Oracle : ℝ)

noncomputable def rootInclusiveArea
    (p : CoordinatePolicy) (f : Oracle → ℝ) : ℝ :=
  ∑ m : Fin 4,
    expectedPosteriorVariance f (fun ω => transcript p ω m.1)

noncomputable def bellmanOptimalArea (f : Oracle → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ p : CoordinatePolicy, legalPolicy p ∧
    a = rootInclusiveArea p f}

/-- Claim 61102: the exact three-function witness, its depth gap, Walsh mass,
    and Bellman-optimal root-inclusive area. -/
def exactThreeDepthTwoMixtureClaim61102 : Prop :=
  T₁ ≠ T₂ ∧
    T₁ ≠ T₃ ∧
    T₂ ≠ T₃ ∧
    (∀ i : Fin 3, minimumDeterministicDepth (componentValue i) 2) ∧
    minimumDeterministicDepth mixtureTarget 3 ∧
    nonconstantWalshMass mixtureTarget = (5 : ℝ) / 3 ∧
    bellmanOptimalArea mixtureTarget = (53 : ℝ) / 36

end

end MathlibPlus.Open.ResearchFormalization.R61102Claim61102
