import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0140

open scoped BigOperators Classical
noncomputable section

abbrev RankFiveModel (p : Nat) := Fin 5 → ZMod p

def claim_5855 : Prop :=
  ∀ p : Nat, p.Prime → 2 < p →
    ∀ h : RankFiveModel p,
      ∃ i j a b c : ZMod p, h = ![i, j, a, b, c]

def xModel {p : Nat} (h : RankFiveModel p) : RankFiveModel p :=
  ![h 0, h 1, h 2 + h 0, h 3 + h 1, h 4]

def yModel {p : Nat} (h : RankFiveModel p) : RankFiveModel p :=
  ![h 0, h 1, h 2, h 3 + h 0, h 4 + h 1]

def gModel {p : Nat} (h : RankFiveModel p) : RankFiveModel p :=
  ![h 0, h 1, h 2 + h 0 * (h 0 - 1),
    h 3 + (2 * h 0 - 1) * h 1, h 4 + h 1 ^ 2]

def claim_5856 : Prop :=
  ∀ p : Nat, p.Prime → 2 < p →
    Function.Bijective (@xModel p) ∧
      Function.Bijective (@yModel p) ∧
        Function.Bijective (@gModel p) ∧
          (∀ h : RankFiveModel p,
            xModel h = ![h 0, h 1, h 2 + h 0, h 3 + h 1, h 4] ∧
              yModel h = ![h 0, h 1, h 2, h 3 + h 0, h 4 + h 1] ∧
                gModel h =
                  ![h 0, h 1, h 2 + h 0 * (h 0 - 1),
                    h 3 + (2 * h 0 - 1) * h 1, h 4 + h 1 ^ 2])

end

end MathlibPlus.Open.ResearchBatch.D0140
