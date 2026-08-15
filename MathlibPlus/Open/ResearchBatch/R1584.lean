import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R1584

def PerfectGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G,
    g ∈ Subgroup.closure (Set.range (fun p : G × G =>
      p.1 * p.2 * p.1⁻¹ * p.2⁻¹))

def NoCommonNontrivialQuotient (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ (Q : Type) [Group Q], Nontrivial Q →
    ¬ ∃ (φ : G →* Q) (ψ : H →* Q),
      Function.Surjective φ ∧ Function.Surjective ψ

def twoFactorGoursatSplitting_claim39383 : Prop :=
  ∀ (Gi Gj : Type*) [Group Gi] [Group Gj],
    PerfectGroup Gi → PerfectGroup Gj →
    NoCommonNontrivialQuotient Gi Gj →
    ∀ K : Subgroup (Gi × Gj),
      (∀ g : Gi, ∃ h : Gj, (g, h) ∈ K) →
      (∀ h : Gj, ∃ g : Gi, (g, h) ∈ K) →
      K = ⊤

end MathlibPlus.Open.ResearchBatch.R1584
