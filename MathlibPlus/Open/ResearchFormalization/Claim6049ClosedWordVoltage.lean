import MathlibPlus.Open.VoltageLiftedOrbitFormula6051

namespace MathlibPlus.Open.ResearchFormalization.Claim6049ClosedWordVoltage

/-- Claim 6049: on every base orbit, a chosen basepoint and the signed-generator
closed-word voltages determine the additive subgroup `W_O`. -/
def closedWordVoltageSubgroup_claim6049 : Prop :=
  ∀ {p : ℕ} [Fact p.Prime]
    {B I : Type*} [Fintype B]
    (r : I → Equiv.Perm B) (β : I → B → ZMod p),
    ∃ W_O : Set B → AddSubgroup (ZMod p),
      ∀ O : Set B, O ∈ Set.range (MathlibPlus.Open.LiftedOrbit.baseOrbit r) →
        ∃ b₀ : B,
          O = MathlibPlus.Open.LiftedOrbit.baseOrbit r b₀ ∧
          b₀ ∈ O ∧
          (let closed : Set (ZMod p) :=
            {v | ∃ w : List (MathlibPlus.Open.LiftedOrbit.Letter I),
              MathlibPlus.Open.LiftedOrbit.baseWord r w b₀ = b₀ ∧
                (MathlibPlus.Open.LiftedOrbit.liftWord r β w (0, b₀)).1 = v}
           (∀ v : ZMod p, v ∈ closed → v ∈ W_O O) ∧
           (∀ S : AddSubgroup (ZMod p),
             (∀ v : ZMod p, v ∈ closed → v ∈ S) → W_O O ≤ S))

end MathlibPlus.Open.ResearchFormalization.Claim6049ClosedWordVoltage
