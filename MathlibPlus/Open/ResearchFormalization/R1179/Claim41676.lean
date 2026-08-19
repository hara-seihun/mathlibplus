import MathlibPlus.Open.ResearchFormalization.R1179.Claim31909

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim41676

open MathlibPlus.Open.ResearchFormalization.R1179.Claim31909

noncomputable section

/-- The exact five-square census has one natural-C₅ partition breaker, namely
    the thick-thin connection, and that row has the stated intrinsic action. -/
def claim41676 : Prop :=
  ∃ rows : Fin 5 → Set G,
    (∀ i : Fin 5, fiveSquareRow (rows i)) ∧
    (∀ i j : Fin 5,
      graphIsomorphism (rows i) (rows j) → i = j) ∧
    (∀ S : Set G, fiveSquareRow S →
      ∃ i : Fin 5, graphIsomorphism S (rows i)) ∧
    ∃ i : Fin 5,
      rows i = thickThinConnection ∧
      ¬ preservesNaturalC5Partition (rows i) ∧
      (∃ θ : D10 →* MulAut IntrinsicBase,
        ∃ q : D10 →* Equiv.Perm (ZMod 5 × Bool),
          ∃ φ : IntrinsicGroup θ →* Equiv.Perm G,
            intrinsicTenFibreData (rows i) θ q φ) ∧
      (∀ j : Fin 5,
        ¬ preservesNaturalC5Partition (rows j) ↔ j = i)

end

end MathlibPlus.Open.ResearchFormalization.R1179.Claim41676
