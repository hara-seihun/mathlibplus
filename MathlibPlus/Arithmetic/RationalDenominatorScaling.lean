import Mathlib

namespace MathlibPlus.Arithmetic

/--
Claim 44266.  For a positive denominator `q`, this is the exact integer
form of the centered rational transition.  Feasible states are represented
by `|V| ≤ q * (N + 2)`; the two displayed next-state bounds use the next
cutoff's corresponding `q * (N + 3)` bound.  The numerator and the chosen
initial state do not enter this local transition identity.
-/
theorem rationalDenominatorScaling_claim44266
    (q : ℕ) (hq : 0 < q) (N : ℕ) (V : ℤ) :
    let Q : ℤ := q
    let step : Bool → ℤ := fun d =>
      2 * V + Q * ((N : ℤ) + 1) * (1 - 2 * (if d then 1 else 0))
    let feasible : ℤ → Prop := fun W => |W| ≤ Q * ((N : ℤ) + 2)
    (feasible V →
      (((|step false| ≤ Q * ((N : ℤ) + 3)) ∧
        (|step true| ≤ Q * ((N : ℤ) + 3))) ↔ |V| ≤ Q)) := by
  dsimp
  intro hV
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hN : (0 : ℤ) ≤ (N : ℤ) := by omega
  have hqN1 : (0 : ℤ) ≤ (q : ℤ) * ((N : ℤ) + 1) := by
    positivity
  have hqN3 : (0 : ℤ) ≤ (q : ℤ) * ((N : ℤ) + 3) := by
    positivity
  constructor
  · intro hboth
    norm_num at hboth
    rcases abs_le.mp hboth.1 with ⟨h0l, h0u⟩
    rcases abs_le.mp hboth.2 with ⟨h1l, h1u⟩
    apply abs_le.mpr
    constructor <;> nlinarith [h0l, h0u, h1l, h1u]
  · intro hbound
    norm_num at hbound ⊢
    rcases abs_le.mp hbound with ⟨hVl, hVu⟩
    constructor <;> apply abs_le.mpr <;> constructor <;>
      nlinarith [hN, hqN1, hqN3]

end MathlibPlus.Arithmetic
