import Mathlib.Data.Finset.Card

namespace MathlibPlus.Algebra.FiniteAdapterExhaustion

/-- Failures on a finite proposed family are exactly a scoped statement; an
exhaustiveness hypothesis is needed to transfer them to all adapters. -/
theorem scoped_failure_and_exhaustion
    {α : Type*} (A : Finset α) (Works : α → Prop)
    (hfail : ∀ a ∈ A, ¬ Works a) :
    (∀ a ∈ A, ¬ Works a) ∧
      ((∀ a, a ∈ A) → ∀ a, ¬ Works a) := by
  refine ⟨hfail, ?_⟩
  intro hexhaust a ha
  exact (hfail a (hexhaust a)) ha

/-- In the absence of exhaustion, finite failure data does not imply a
universal no-go statement. -/
theorem finite_failure_not_universal :
    ∃ (α : Type) (A : Finset α) (Works : α → Prop),
      (∀ a ∈ A, ¬ Works a) ∧ ¬ (∀ a, ¬ Works a) := by
  refine ⟨Bool, {false}, (· = true), ?_, ?_⟩
  · intro a ha hworks
    have ha' : a = false := Finset.mem_singleton.mp ha
    simpa [ha'] using hworks
  · intro h
    exact (h true) rfl

end MathlibPlus.Algebra.FiniteAdapterExhaustion
