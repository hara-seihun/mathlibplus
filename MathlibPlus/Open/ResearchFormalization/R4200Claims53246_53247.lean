import MathlibPlus.Open.ResearchFormalization.Claim53248

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4200

noncomputable section

/-- The exact finite persistent experiment used for Statement 2.  The
`freshOrderProbability`, `expectedFreshYPosition`, and posterior-area
quantities are the finite Plackett--Luce and cached-opposite-label model
supplied through Claim 53248. -/
def freshPlackettLuceRatesAndArea_claim53246 : Prop :=
  ∀ (n : ℕ) (ε : ℝ),
    2 ≤ n → 0 < ε → ε < 1 →
      cancelledLiteralFamily n ε ∧
      cancelledRate n ε = (1 - ε) / (n : ℝ) ∧
      (∀ i : Fin (n + 1), i.val < n →
        freshRate n ε i = (1 - ε) / (n : ℝ)) ∧
      freshRate n ε (yCoordinate n) = ε ∧
      (∀ π : Equiv.Perm (Fin (n + 1)),
        freshOrderProbability n ε π =
          ∏ k : Fin (n + 1),
            freshRate n ε (π k) /
              ∑ j : Fin (n + 1),
                if (π.symm j).val ≥ k.val then freshRate n ε j else 0) ∧
      expectedFreshYPosition n ε =
        1 + (n : ℝ) * ((1 - ε) / (n : ℝ)) /
          (((1 - ε) / (n : ℝ)) + ε) ∧
      (∀ (π : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 2)),
        posteriorVarianceAtFreshTime n ε π t =
          if t.val < (π.symm (yCoordinate n)).val + 1 then ε ^ 2 else 0) ∧
      persistentPlackettLuceArea n ε =
        ε ^ 2 *
          (1 + (n : ℝ) * ((1 - ε) / (n : ℝ)) /
            (((1 - ε) / (n : ℝ)) + ε))

/-- The exact reserve model uses a uniform law on the Boolean marking maps;
the displayed bracket is its conditional residual-order contribution. -/
def exactPathMarkedReserveFormula_claim53247 : Prop :=
  ∀ (n : ℕ) (ε : ℝ),
    2 ≤ n → 0 < ε → ε < 1 →
      cancelledLiteralFamily n ε ∧
      (∀ A : Fin n → Bool,
        pathMarkedBracket n ε A =
          1 + ((n - markedCount A : ℕ) : ℝ) * cancelledRate n ε /
            (ε + ((markedCount A + 1 : ℕ) : ℝ) * cancelledRate n ε)) ∧
      inheritedOrderPathMarkedReserve n ε =
        ε ^ 2 *
          ∑ A : Fin n → Bool,
            (1 / (2 : ℝ) ^ n) * pathMarkedBracket n ε A ∧
      inheritedOrderPathMarkedReserve n ε =
        binomialPathMarkedReserve n ε ∧
      binomialPathMarkedReserve n ε =
        ε ^ 2 *
          Finset.sum (Finset.range (n + 1)) (fun m =>
            ((Nat.choose n m : ℝ) / (2 : ℝ) ^ n) *
              (1 + ((n - m : ℕ) : ℝ) * cancelledRate n ε /
                (ε + ((m + 1 : ℕ) : ℝ) * cancelledRate n ε)))

end

end MathlibPlus.Open.ResearchFormalization.R4200
