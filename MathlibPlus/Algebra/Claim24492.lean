import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra.Claim24492

lemma monomialEndpointMod (n : ℕ) (a : ℤ) :
    Int.ModEq 4 (a * (2 : ℤ) ^ n) (a * (-2 : ℤ) ^ n) := by
  rw [Int.modEq_iff_dvd]
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero =>
      refine ⟨-a, ?_⟩
      ring
    | succ n =>
      refine ⟨a * ((-2 : ℤ) ^ n - (2 : ℤ) ^ n), ?_⟩
      simp [pow_succ]
      ring

/-- Claim 24492: a monic integral polynomial of even degree has congruent
endpoint values at `2` and `-2` modulo `4`. -/
theorem evenDegreeMonicEndpointCongruence
    (ℓ : Polynomial ℤ) (_hmonic : ℓ.Monic) (_heven : Even ℓ.natDegree) :
    Int.ModEq 4 (Polynomial.eval 2 ℓ) (Polynomial.eval (-2) ℓ) := by
  have hgeneral : ∀ p : Polynomial ℤ,
      Int.ModEq 4 (Polynomial.eval 2 p) (Polynomial.eval (-2) p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
        simpa [Polynomial.eval_monomial] using monomialEndpointMod n a
  exact hgeneral ℓ

end MathlibPlus.Algebra.Claim24492
