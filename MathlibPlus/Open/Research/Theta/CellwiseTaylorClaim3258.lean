import Mathlib
import MathlibPlus.Open.ResearchFormalization.Theta

open scoped BigOperators

namespace MathlibPlus.Open.Research.Theta

noncomputable section

private def thetaH (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      iteratedDeriv (i.val + j.val) kernel t)

private def thetaCell (j : Fin 65) : Set ℝ :=
  Set.Icc ((j.val : ℝ) / 160) (((j.val + 1 : ℕ) : ℝ) / 160)

private def thetaCellCenter (j : Fin 65) : ℝ :=
  ((2 * j.val + 1 : ℕ) : ℝ) / 320

private def multinomialCoefficient
    (q m : ℕ) (a : Fin m → Fin (q + 1)) : ℕ :=
  if (∑ i : Fin m, (a i).val) = q then
    Nat.factorial q / ∏ i : Fin m, Nat.factorial (a i).val
  else 0

private def determinantDerivativeLeibniz
    (m q : ℕ) (t : ℝ) : Prop :=
  iteratedDeriv q (thetaH m) t =
    (-1 : ℝ) ^ (m * (m - 1) / 2) *
      ∑ σ : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ a : Fin m → Fin (q + 1),
            (multinomialCoefficient q m a : ℝ) *
              ∏ i : Fin m,
                iteratedDeriv
                  (i.val + (σ i).val + (a i).val) kernel t

def cellwiseTaylorDeterminantLowerBound_claim3258 : Prop :=
  let ρ : ℝ := 1 / 320
  (∀ j : Fin 65, ∀ m : ℕ,
    (m = 2 ∨ m = 3 ∨ m = 4) →
      ∀ q : ℕ, q ≤ 9 → ∀ t : ℝ,
        t ∈ thetaCell j →
          determinantDerivativeLeibniz m q t) ∧
    (∀ j : Fin 65, ∀ m : ℕ,
      (m = 2 ∨ m = 3 ∨ m = 4) → ∀ t : ℝ,
        t ∈ thetaCell j →
          thetaH m t ≥
            thetaH m (thetaCellCenter j) -
              ∑ q ∈ Finset.Icc 1 8,
                |iteratedDeriv q (thetaH m) (thetaCellCenter j)| *
                  ρ ^ q / (Nat.factorial q : ℝ) -
              sSup {v : ℝ | ∃ s : ℝ,
                s ∈ thetaCell j ∧
                  v = |iteratedDeriv 9 (thetaH m) s|} *
                ρ ^ 9 / (Nat.factorial 9 : ℝ))

end
end MathlibPlus.Open.Research.Theta
