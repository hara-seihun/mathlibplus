import Mathlib

namespace MathlibPlus.Open.Research1499

noncomputable section
open scoped Classical

abbrev B3 := ZMod 3 × ZMod 3
abbrev BPerm := Equiv.Perm B3

def commonLineVector : B3 := (0, 1)

def TranslationB (d : B3) : BPerm := Equiv.addRight d

def NormalizedCommonLineChart (φ : BPerm) : Prop :=
  φ (0, 0) = (0, 0) ∧
    ∀ x : B3, φ (x + commonLineVector) = φ x + commonLineVector

def ChartForm (φ : BPerm) (σ : Equiv.Perm (ZMod 3)) (k : ZMod 3 → ZMod 3) : Prop :=
  σ 0 = 0 ∧ k 0 = 0 ∧ ∀ x y : ZMod 3, φ (x, y) = (σ x, y + k x)

def AffineCommonLineChart (φ : BPerm) : Prop :=
  ∃ A : B3 ≃+ B3, ∃ b : B3, ∀ x, φ x = A x + b

def TranslationSetB : Set BPerm := {p | ∃ d : B3, p = TranslationB d}
def TranslationSubgroupB : Subgroup BPerm := Subgroup.closure TranslationSetB

def ConjugateTranslationSetB (φ : BPerm) : Set BPerm :=
  {p | ∃ d : B3, p = φ.symm * TranslationB d * φ}
def ConjugateTranslationSubgroupB (φ : BPerm) : Subgroup BPerm :=
  Subgroup.closure (ConjugateTranslationSetB φ)

def RegularOnB (K : Subgroup BPerm) : Prop :=
  Fintype.card K = 9 ∧ ∀ x y : B3, ∃! p : K, (p : BPerm) x = y

def UnequalChart (φ : BPerm) : Prop :=
  NormalizedCommonLineChart φ ∧ ¬ AffineCommonLineChart φ ∧
    RegularOnB (ConjugateTranslationSubgroupB φ) ∧
    TranslationSubgroupB ⊓ ConjugateTranslationSubgroupB φ =
      Subgroup.closure ({TranslationB commonLineVector} : Set BPerm) ∧
    Fintype.card (Subgroup.closure
      (TranslationSetB ∪ ConjugateTranslationSetB φ)) = 27

/-- Claim 37888. -/
def normalizedCommonLineQuotientCharts_claim37888 : Prop :=
  (∀ φ : BPerm, NormalizedCommonLineChart φ →
    ∃ σ : Equiv.Perm (ZMod 3), ∃ k : ZMod 3 → ZMod 3,
      ChartForm φ σ k ∧
      ∀ σ' : Equiv.Perm (ZMod 3), ∀ k' : ZMod 3 → ZMod 3,
        ChartForm φ σ' k' → σ' = σ ∧ k' = k) ∧
  (∀ σ : Equiv.Perm (ZMod 3), ∀ k : ZMod 3 → ZMod 3,
    σ 0 = 0 → k 0 = 0 →
      ∃ φ : BPerm, NormalizedCommonLineChart φ ∧ ChartForm φ σ k)

/-- Claim 37890. -/
def exactChartCensusAndUnequalQuotientGeneration_claim37890 : Prop :=
  Fintype.card {φ : BPerm // NormalizedCommonLineChart φ} = 18 ∧
    Fintype.card {φ : BPerm // NormalizedCommonLineChart φ ∧
      AffineCommonLineChart φ ∧
      ConjugateTranslationSubgroupB φ = TranslationSubgroupB} = 6 ∧
    Fintype.card {φ : BPerm // UnequalChart φ} = 12 ∧
    ∀ φ : BPerm, UnequalChart φ →
      Fintype.card (Subgroup.closure
        (TranslationSetB ∪ ConjugateTranslationSetB φ)) = 27

end
end MathlibPlus.Open.Research1499
