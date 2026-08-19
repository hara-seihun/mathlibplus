import Mathlib
import MathlibPlus.Open.CayleyCI.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalization.R61267OrientationSpectator

open MathlibPlus.Open.CayleyCI

/-- Claim 61267: a directed Cayley defect on a coprime abelian Hall factor
lifts through any additive spectator containing an element of order greater
than two, producing an ordinary undirected Cayley defect. -/
def coprimeOrientationSpectator_claim61267 : Prop :=
  ∀ (A H : Type*) [AddCommGroup A] [Fintype A]
    [AddCommGroup H] [Fintype H],
    Nat.Coprime (Fintype.card A) (Fintype.card H) →
      ∀ a : A, 2 < addOrderOf a →
        ∀ S T : Set H,
          S ⊆ (Set.univ : Set H) \ {0} →
            T ⊆ (Set.univ : Set H) \ {0} →
              (∀ β : H ≃+ H, Set.image β S ≠ T) →
                ∀ f : H ≃ H,
                  f 0 = 0 →
                    (∀ x y : H,
                      (y - x ∈ S ↔ f y - f x ∈ T)) →
                      let signedS : Set (A × H) :=
                        (({a} : Set A) ×ˢ S) ∪
                          (({-a} : Set A) ×ˢ Set.image Neg.neg S)
                      let signedT : Set (A × H) :=
                        (({a} : Set A) ×ˢ T) ∪
                          (({-a} : Set A) ×ˢ Set.image Neg.neg T)
                      let F : A × H ≃ A × H :=
                        Equiv.prodCongr (Equiv.refl A) f
                      let ordinaryCI : Prop :=
                        ∀ R : Set (A × H),
                          AddIdentityFreeInverseClosed (A × H) R →
                            AddOrdinaryUndirectedCIConnectionSet (A × H) R
                      AddIdentityFreeInverseClosed (A × H) signedS ∧
                        AddIdentityFreeInverseClosed (A × H) signedT ∧
                        (∀ x y : A × H,
                          (y - x ∈ signedS ↔ F y - F x ∈ signedT)) ∧
                        (∀ α : (A × H) ≃+ (A × H),
                          Set.image α signedS ≠ signedT) ∧
                        ¬ ordinaryCI

end MathlibPlus.Open.ResearchFormalization.R61267OrientationSpectator
