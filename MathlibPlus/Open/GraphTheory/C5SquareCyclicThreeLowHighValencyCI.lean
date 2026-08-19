import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

abbrev C5SquareCyclicThreeCarrier := (Fin 2 → ZMod 5) × ZMod 3

def identityFree (S : Set C5SquareCyclicThreeCarrier) : Prop :=
  (0 : C5SquareCyclicThreeCarrier) ∉ S

def inverseClosed (S : Set C5SquareCyclicThreeCarrier) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def ordinaryCayleyIsomorphism
    (S T : Set C5SquareCyclicThreeCarrier)
    (e : C5SquareCyclicThreeCarrier ≃ C5SquareCyclicThreeCarrier) : Prop :=
  ∀ x y : C5SquareCyclicThreeCarrier,
    y - x ∈ S ↔ e y - e x ∈ T

/-- Claim 59377: the exact low-valency and complementary high-valency
ordinary undirected CI statement on `C₅² × C₃`, with no connectedness,
directedness, or whole-group strengthening. -/
def c5SquareCyclicThreeLowHighValencyCI : Prop :=
  ∀ (S T : Set C5SquareCyclicThreeCarrier),
    identityFree S →
      identityFree T →
        inverseClosed S →
          inverseClosed T →
            (Set.ncard S ≤ 20 ∨ 54 ≤ Set.ncard S) →
              (Set.ncard T ≤ 20 ∨ 54 ≤ Set.ncard T) →
                ∀ e : C5SquareCyclicThreeCarrier ≃
                    C5SquareCyclicThreeCarrier,
                  ordinaryCayleyIsomorphism S T e →
                    ∃ α : C5SquareCyclicThreeCarrier ≃+
                        C5SquareCyclicThreeCarrier,
                      Set.image α S = T

end

end MathlibPlus.Open.GraphTheory
