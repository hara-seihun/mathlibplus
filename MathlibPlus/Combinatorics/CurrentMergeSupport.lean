import Mathlib.Algebra.Group.Finsupp
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- Claim 5676: a width-`w` binary current merge uses at most `2*w`
persistent/temporary support slots before coalescing.

The two child currents are represented by finitely supported maps.  Their sum has
support inside the union of the child supports; the parent width hypothesis is
retained explicitly rather than inferred from cancellation. -/
theorem currentMergeSupport_claim5676
    {ι M : Type*} [DecidableEq ι] [AddZeroClass M]
    (w : ℕ) (q₁ q₂ : ι →₀ M)
    (h₁ : q₁.support.card ≤ w) (h₂ : q₂.support.card ≤ w)
    (hparent : (q₁ + q₂).support.card ≤ w) :
    q₁.support.card ≤ w ∧
    q₂.support.card ≤ w ∧
    (q₁ + q₂).support ⊆ q₁.support ∪ q₂.support ∧
    (q₁.support ∪ q₂.support).card ≤ 2 * w ∧
    (q₁ + q₂).support.card ≤ w := by
  refine ⟨h₁, h₂, Finsupp.support_add, ?_, hparent⟩
  calc
    (q₁.support ∪ q₂.support).card ≤ q₁.support.card + q₂.support.card :=
      Finset.card_union_le _ _
    _ ≤ w + w := Nat.add_le_add h₁ h₂
    _ = 2 * w := by omega

end MathlibPlus.Combinatorics
