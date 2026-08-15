import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.NumberTheory.Claim8276

/-- The exact three-variable arithmetic sum from the admitted supporting statement. -/
noncomputable def arithmeticSum (N : ℕ) (χ : DirichletCharacter ℂ N)
    (w v : ℂ) : ℂ :=
  ∑' Q : ℕ, ∑' d : ℕ, ∑' m : ℕ,
    if 0 < Q ∧ 0 < d ∧ 0 < m ∧
        Nat.Coprime (Q * d * m) N ∧ Nat.Coprime Q d ∧
        Nat.Coprime Q m ∧ Nat.Coprime d m then
      ((ArithmeticFunction.moebius Q : ℤ) : ℂ) /
          Complex.cpow (Q : ℂ) (1 + w) *
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) ^ 2 /
          Complex.cpow (d : ℂ) (1 + w + v) *
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
          χ (m : ZMod N) /
          Complex.cpow (m : ℂ) (1 + v)
    else 0

/-- The incomplete zeta function from the admitted supporting statement. -/
noncomputable def incompleteZeta (N : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * ∏' p : ℕ,
    if p.Prime ∧ p ∣ N then
      1 - Complex.cpow (p : ℂ) (-s)
    else 1

/-- The Dirichlet L-series used by the admitted notation `L(s,χ)`. -/
noncomputable def dirichletL (N : ℕ) (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  LSeries (fun n => χ (n : ZMod N)) s

/-- The ratio in the Mellin corner assertion. -/
noncomputable def cornerRatio (N : ℕ) (w v : ℝ) : ℂ :=
  incompleteZeta N (1 + ((w + v : ℝ) : ℂ)) /
    incompleteZeta N (1 + (w : ℂ))

/-- The normalized arithmetic sum in the two iterated-limit assertions. -/
noncomputable def normalizedArithmeticSum (N : ℕ) (χ : DirichletCharacter ℂ N)
    (w v : ℝ) : ℂ :=
  dirichletL N χ 1 * arithmeticSum N χ (w : ℂ) (v : ℂ)

noncomputable def positiveRightNhd : Filter ℝ :=
  nhdsWithin 0 (Set.Ioi 0)

/-- Path-dependent Mellin corner. -/
def pathDependentMellinCorner_claim8276 : Prop :=
  ∀ N : ℕ, 1 < N →
    ∀ χ : DirichletCharacter ℂ N,
      χ (-1 : ZMod N) = (-1 : ℂ) →
        Asymptotics.IsEquivalent
            (nhdsWithin (0, 0)
              {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2})
            (fun p => cornerRatio N p.1 p.2)
            (fun p => (p.1 / (p.1 + p.2) : ℂ)) ∧
        (∃ inner : ℝ → ℂ,
          (∀ᶠ w in positiveRightNhd,
            Filter.Tendsto
              (fun v : ℝ => normalizedArithmeticSum N χ w v)
              positiveRightNhd (𝓝 (inner w))) ∧
          Filter.Tendsto inner positiveRightNhd (𝓝 (1 : ℂ))) ∧
        (∃ inner : ℝ → ℂ,
          (∀ᶠ v in positiveRightNhd,
            Filter.Tendsto
              (fun w : ℝ => normalizedArithmeticSum N χ w v)
              positiveRightNhd (𝓝 (inner v))) ∧
          Filter.Tendsto inner positiveRightNhd (𝓝 (0 : ℂ)))

end MathlibPlus.NumberTheory.Claim8276
