import Mathlib

namespace MathlibPlus.Open.Analysis.NumberTheory

noncomputable def mobiusReal (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℤ)

noncomputable def windowProfileForPrimitiveDirection (t : ℝ) : ℝ :=
  ∫ r in t..(Real.exp 2 * t), Real.sqrt r * Real.exp (-r)

noncomputable def squarefreeRadialSum (q : ℕ) (c : ℝ) : ℝ :=
  ∑' d : ℕ+,
    if Nat.Coprime d.1 q then
      mobiusReal d.1 ^ 2 * (d.1 : ℝ)⁻¹ *
        windowProfileForPrimitiveDirection (c / (d.1 : ℝ) ^ 2)
    else 0

noncomputable def untruncatedRieszBlockEnergy (X : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑' m : ℕ+, ∑' n : ℕ+,
      mobiusReal m.1 * mobiusReal n.1 *
        ((m.1 : ℝ) * (n.1 : ℝ)) /
          Real.rpow ((m.1 : ℝ) ^ 2 + (n.1 : ℝ) ^ 2) (3 / 2 : ℝ) *
        windowProfileForPrimitiveDirection
          (X * ((m.1 : ℝ) ^ 2 + (n.1 : ℝ) ^ 2) /
            ((m.1 : ℝ) ^ 2 * (n.1 : ℝ) ^ 2))

noncomputable def primitiveDirectionTerm (X : ℝ) (a b : ℕ+) : ℝ :=
  mobiusReal a.1 * mobiusReal b.1 *
    ((a.1 : ℝ) * (b.1 : ℝ)) /
      Real.rpow ((a.1 : ℝ) ^ 2 + (b.1 : ℝ) ^ 2) (3 / 2 : ℝ) *
    squarefreeRadialSum (a.1 * b.1)
      (X * ((a.1 : ℝ) ^ 2 + (b.1 : ℝ) ^ 2) /
        ((a.1 : ℝ) ^ 2 * (b.1 : ℝ) ^ 2))

def natSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

def primitiveDirectionEnergyDecompositionClaim : Prop :=
  ∀ X : ℝ, 0 < X →
    (untruncatedRieszBlockEnergy X =
        (1 / 2 : ℝ) *
          ∑' p : {p : ℕ+ × ℕ+ // Nat.Coprime p.1.1 p.2.1},
            primitiveDirectionTerm X p.1.1 p.1.2) ∧
      (∀ a b : ℕ+, Nat.Coprime a.1 b.1 →
        (¬ natSquarefree a.1 ∨ ¬ natSquarefree b.1) →
          primitiveDirectionTerm X a b = 0)

end MathlibPlus.Open.Analysis.NumberTheory
