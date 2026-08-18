import MathlibPlus.Open.Analysis.OracleAreaDepthTwoFiveFourths

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootDepthTwoClaim61083

noncomputable section
open Classical

abbrev Sign := MathlibPlus.Open.Analysis.Sign
abbrev Oracle (I : Type*) := I → Sign
abbrev BooleanFunction (I : Type*) := Oracle I → Sign
abbrev RootedAtom (I : Type*) :=
  BooleanFunction I × (MathlibPlus.Open.Analysis.SignDecisionTree I ×
    MathlibPlus.Open.Analysis.SignDecisionTree I)
abbrev RootedLaw (I : Type*) := RootedAtom I → ℝ
abbrev RevealTranscript (I : Type*) := List (I × Sign)
abbrev RevealPolicy (I : Type*) := RevealTranscript I → Option I

def lawSupport {I : Type*} (Λ : RootedLaw I) : Set (RootedAtom I) :=
  {A | 0 < Λ A}

def realProbabilityLaw {α : Type*} (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑' a, p a = 1

def probabilityLaw {I : Type*} (Λ : RootedLaw I) : Prop :=
  realProbabilityLaw Λ

def finiteSupport {I : Type*} (Λ : RootedLaw I) : Prop :=
  Set.Finite (lawSupport Λ)

def atomFunction {I : Type*} (A : RootedAtom I) : BooleanFunction I :=
  A.1

def negativeBranch {I : Type*} (A : RootedAtom I) :
    MathlibPlus.Open.Analysis.SignDecisionTree I :=
  A.2.1

def positiveBranch {I : Type*} (A : RootedAtom I) :
    MathlibPlus.Open.Analysis.SignDecisionTree I :=
  A.2.2

def rootedTree {I : Type*} (r : I) (A : RootedAtom I) :
    MathlibPlus.Open.Analysis.SignDecisionTree I :=
  .query r (negativeBranch A) (positiveBranch A)

def commonRootRepresentation {I : Type*} (r : I) (A : RootedAtom I) : Prop :=
  MathlibPlus.Open.Analysis.SignDecisionTree.depth (rootedTree r A) ≤ 2 ∧
    ∀ O,
      MathlibPlus.Open.Analysis.SignDecisionTree.evaluate
          (rootedTree r A) O = atomFunction A O

def commonRootLawAt {I : Type*} (r : I) (Λ : RootedLaw I) : Prop :=
  probabilityLaw Λ ∧
    finiteSupport Λ ∧
      ∀ A, A ∈ lawSupport Λ → commonRootRepresentation r A

def lawMean {I : Type*} (Λ : RootedLaw I) (O : Oracle I) : ℝ :=
  ∑' A, Λ A *
    MathlibPlus.Open.Analysis.signValue (atomFunction A O)

def branchTree {I : Type*} (A : RootedAtom I) (ε : Sign) :
    MathlibPlus.Open.Analysis.SignDecisionTree I :=
  if ε = MathlibPlus.Open.Analysis.posSign then positiveBranch A
  else negativeBranch A

def branchNonconstant {I : Type*} (A : RootedAtom I) (ε : Sign) : Prop :=
  MathlibPlus.Open.Analysis.SignFunctionNonconstant
    (fun O =>
      MathlibPlus.Open.Analysis.SignDecisionTree.evaluate (branchTree A ε) O)

def branchMass {I : Type*} (Λ : RootedLaw I) (ε : Sign) : ℝ :=
  ∑' A,
    if A ∈ lawSupport Λ ∧ branchNonconstant A ε then Λ A else 0

def transcriptCompatible {I : Type*}
    (h : RevealTranscript I) (O : Oracle I) : Prop :=
  ∀ p ∈ h, O p.1 = p.2

def recordedSign {I : Type*} (h : RevealTranscript I) (i : I) : Option Sign :=
  (h.find? (fun p => p.1 = i)).map Prod.snd

def transcriptStep {I : Type*} (h : RevealTranscript I)
    (O : Oracle I) (a : Option I) : RevealTranscript I :=
  match a with
  | none => h
  | some i => h ++ [(i, O i)]

def historyAt {I : Type*} (π : RevealPolicy I) (O : Oracle I) : ℕ → RevealTranscript I
  | 0 => []
  | m + 1 =>
      let h := historyAt π O m
      transcriptStep h O (π h)

def legalPolicy {I : Type*} (π : RevealPolicy I) : Prop :=
  ∀ h i, π h = some i → recordedSign h i = none

def revealFiltration {I : Type*} (π : RevealPolicy I) (m : ℕ) :
    MeasurableSpace (Oracle I) :=
  MeasurableSpace.comap
    (fun O => historyAt π O m)
    (⊤ : MeasurableSpace (RevealTranscript I))

def limitFiltration {I : Type*} (π : RevealPolicy I) : MeasurableSpace (Oracle I) :=
  ⨆ m : ℕ, revealFiltration π m

def measurableIn {Ω : Type*} (m : MeasurableSpace Ω)
    (f : Ω → ℝ) : Prop :=
  @Measurable Ω ℝ m inferInstance f

def cellMeasurable {I : Type*} (μ : Oracle I → ℝ)
    (h : RevealTranscript I) : Prop :=
  ∀ O O', transcriptCompatible h O → transcriptCompatible h O' → μ O = μ O'

def stoppedWhenMeasurable {I : Type*} (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  ∀ O m,
    (π (historyAt π O m) = none ↔
      cellMeasurable μ (historyAt π O m))

def limitDeterminesTarget {I : Type*} (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  measurableIn (limitFiltration π) μ

def policyArea {I : Type*} (P : Measure (Oracle I))
    (π : RevealPolicy I) (μ : Oracle I → ℝ) : ℝ :=
  ∑' m : ℕ,
    MathlibPlus.Open.Analysis.expectedConditionalVariance
      P (revealFiltration π m) μ

def unconditionalVariance {I : Type*} (P : Measure (Oracle I))
    (μ : Oracle I → ℝ) : ℝ :=
  MathlibPlus.Open.Analysis.expectedConditionalVariance
    P (⊥ : MeasurableSpace (Oracle I)) μ

def selector {I : Type*} (r a b : I) : Oracle I → Sign :=
  fun O => if O r = MathlibPlus.Open.Analysis.posSign then O a else O b

def literalTree {I : Type*} (i : I) :
    MathlibPlus.Open.Analysis.SignDecisionTree I :=
  .query i (.leaf MathlibPlus.Open.Analysis.negSign)
    (.leaf MathlibPlus.Open.Analysis.posSign)

def selectorAtom {I : Type*} (r a b : I) : RootedAtom I :=
  (selector r a b, (literalTree b, literalTree a))

def pointRootedLaw {I : Type*} (A : RootedAtom I) : RootedLaw I :=
  fun B => if B = A then 1 else 0

def selectorPolicy {I : Type*} (r a b : I) : RevealPolicy I :=
  fun h =>
    match recordedSign h r with
    | none => some r
    | some s =>
      if s = MathlibPlus.Open.Analysis.posSign then
        if recordedSign h a = none then some a else none
      else if recordedSign h b = none then some b else none

def selectorSharpness61083 {I : Type*} [Countable I]
    (r a b : I) (P : Measure (Oracle I)) : Prop :=
  r ≠ a ∧ r ≠ b ∧ a ≠ b →
    MathlibPlus.Open.Analysis.IndependentUniformSigns P →
      let A := selectorAtom r a b
      let Λ := pointRootedLaw A
      let μ := fun O => lawMean Λ O
      commonRootLawAt r Λ ∧
        branchMass Λ MathlibPlus.Open.Analysis.posSign = 1 ∧
          branchMass Λ MathlibPlus.Open.Analysis.negSign = 1 ∧
            unconditionalVariance P μ = 1 ∧
              legalPolicy (selectorPolicy r a b) ∧
                stoppedWhenMeasurable (selectorPolicy r a b) μ ∧
                  limitDeterminesTarget (selectorPolicy r a b) μ ∧
                    policyArea P (selectorPolicy r a b) μ = 2 ∧
                    (∀ π : RevealPolicy I,
                      legalPolicy π →
                        stoppedWhenMeasurable π μ →
                          limitDeterminesTarget π μ →
                            2 ≤ policyArea P π μ)

/-- Claim 61083: the common-root depth-two class admits one actual adaptive
filtration with the stated root-inclusive variance bound and sharp constant. -/
def commonRootDepthTwoOracleArea_claim61083 : Prop :=
  (∀ (I : Type*) [Countable I] (r : I) (Λ : RootedLaw I)
      (P : Measure (Oracle I)),
      commonRootLawAt r Λ →
        MathlibPlus.Open.Analysis.IndependentUniformSigns P →
          let μ := fun O => lawMean Λ O
          let qPlus := branchMass Λ MathlibPlus.Open.Analysis.posSign
          let qMinus := branchMass Λ MathlibPlus.Open.Analysis.negSign
          ∃ π : RevealPolicy I,
            legalPolicy π ∧
              stoppedWhenMeasurable π μ ∧
                limitDeterminesTarget π μ ∧
                  policyArea P π μ ≤
                    unconditionalVariance P μ +
                      (qPlus ^ 2 + qMinus ^ 2) / 2 ∧
                    unconditionalVariance P μ +
                        (qPlus ^ 2 + qMinus ^ 2) / 2 ≤ 2) ∧
    (∀ (I : Type*) [Countable I] (r a b : I) (P : Measure (Oracle I)),
      selectorSharpness61083 r a b P)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaCommonRootDepthTwoClaim61083
