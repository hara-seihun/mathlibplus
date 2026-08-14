import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 3296: intersecting coefficient-noise balls make a weak pole
unobservable from the first M+1 coefficients. -/
def claim3296 : Prop :=
  ∀ (M : ℕ) (a lam : ℂ) (ε : ℝ),
    ‖a‖ *
      (Finset.sup' (Finset.univ : Finset (Fin (M + 1))) (by simp)
        (fun n : Fin (M + 1) => ‖lam‖ ^ n.1)) ≤ ε →
      let Obs := Fin (M + 1) → ℂ
      let zero : Obs := fun _ => 0
      let pole : Obs := fun n => a * lam ^ n.1
      let ball : Obs → Set Obs := fun center =>
        {observed | ∀ n : Fin (M + 1), ‖observed n - center n‖ ≤ ε}
      ∃ observed : Obs,
        observed ∈ ball zero ∧ observed ∈ ball pole ∧
          ¬ ∃ algorithm : Obs → Bool,
            (∀ z : Obs, z ∈ ball zero → algorithm z = false) ∧
              (∀ z : Obs, z ∈ ball pole → algorithm z = true)

end MathlibPlus.Open.ResearchFormalization
