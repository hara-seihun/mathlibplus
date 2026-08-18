import MathlibPlus.Open.ResearchFormalization.R0335

namespace MathlibPlus.Open.ResearchFormalization.R0335Claim20027

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.TreeSpectral
open MathlibPlus.Open.ResearchFormalization.R0335

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The leaf/card incidence predicate used by all four second-jet channels. -/
def leafCardCondition {n : ℕ}
    (C : TreeClass (n - 1)) (T : TreeClass n) (ell : Fin n) : Prop :=
  representativeIsLeaf T ell ∧ cardDeletionIsomorphism C T ell

/-- The four displayed channel sums, written independently of the channel
selector. -/
def aZeroFormula {n : ℕ}
    (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  ∑ ell : Fin n, if leafCardCondition C T ell then 1 else 0

def aOneFormula {n : ℕ}
    (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  ∑ ell : Fin n,
    if leafCardCondition C T ell then attachmentDegree T ell else 0

def aTwoStarFormula {n : ℕ}
    (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  ∑ ell : Fin n,
    if leafCardCondition C T ell then
      Nat.choose (attachmentDegree T ell) 2
    else 0

def aTwoPathFormula {n : ℕ}
    (C : TreeClass (n - 1)) (T : TreeClass n) : ℕ :=
  ∑ ell : Fin n,
    if leafCardCondition C T ell then attachmentTwoStepWeight T ell else 0

/-- The explicitly stacked rational matrix of the four channels. -/
def secondLeafAttachmentMatrix (n : ℕ) :
    Matrix (TreeClass (n - 1) × Fin 4) (TreeClass n) ℚ :=
  fun r T =>
    if r.2.val = 0 then (aZeroFormula r.1 T : ℚ)
    else if r.2.val = 1 then (aOneFormula r.1 T : ℚ)
    else if r.2.val = 2 then (aTwoStarFormula r.1 T : ℚ)
    else (aTwoPathFormula r.1 T : ℚ)

/-- Claim 20027: the four leaf-attachment channels have the displayed
weights, and their stacking is the second leaf-attachment matrix A_n. -/
def secondLeafAttachmentJet_claim20027 : Prop :=
  ∀ n : ℕ,
    (∀ C : TreeClass (n - 1), ∀ T : TreeClass n,
      a₀ C T = aZeroFormula C T ∧
      a₁ C T = aOneFormula C T ∧
      a₂Star C T = aTwoStarFormula C T ∧
      a₂Path C T = aTwoPathFormula C T) ∧
    attachmentMatrixQ n = secondLeafAttachmentMatrix n

end

end MathlibPlus.Open.ResearchFormalization.R0335Claim20027
