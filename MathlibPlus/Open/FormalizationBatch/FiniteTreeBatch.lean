import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- The exact finite-tree/site-code obstruction in admitted claim 60325. -/
def claim60325 : Prop := by
  classical
  exact ∀ (V V' : Type*) [Finite V] [Finite V']
      (T : SimpleGraph V) (T' : SimpleGraph V'),
      T.IsTree → T'.IsTree →
      (¬ (∃ e : V ≃ V', ∀ v w, T.Adj v w ↔ T'.Adj (e v) (e w))) →
      ∀ (S S' C : Type*) [Finite S] [Finite S']
        (C_T : S → C) (C_T' : S' → C),
        (∀ s s', C_T s = C_T' s' →
          ∃ e : V ≃ V', ∀ v w, T.Adj v w ↔ T'.Adj (e v) (e w)) →
        letI : Fintype S := Fintype.ofFinite S
        letI : Fintype S' := Fintype.ofFinite S'
        let edge : S → S' → Prop := fun s s' => C_T s = C_T' s'
        let neighbourhood : Finset S → Finset S' := fun A =>
          A.biUnion (fun s => Finset.univ.filter (fun s' => edge s s'))
        (∀ s s', ¬ edge s s') ∧
          ∀ A : Finset S, A.Nonempty →
            neighbourhood A = ∅ ∧ ¬ A.card ≤ (neighbourhood A).card

end MathlibPlus.Open.FormalizationBatch
