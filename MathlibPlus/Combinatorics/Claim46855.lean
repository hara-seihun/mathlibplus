-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim46855

open Polynomial

/-!
The source does not expose the GSB local-`h` transform as a Lean definition.
The exact coefficient polynomials and the displayed local sequences are kept as
separate explicit data; no unprovided transform is silently chosen.
-/

noncomputable def P : Polynomial ℚ :=
  1 + 4 * X + 8 * X ^ 2

noncomputable def Q : Polynomial ℚ :=
  1 + 8 * X + 6 * X ^ 2 + 5 * X ^ 3 + 4 * X ^ 4 + 3 * X ^ 5

noncomputable def C : Polynomial ℚ :=
  1 + 12 * X + 46 * X ^ 2 + 93 * X ^ 3 +
    72 * X ^ 4 + 59 * X ^ 5 + 44 * X ^ 6 + 24 * X ^ 7

def localH_P : Fin 2 → ℚ := ![3, 2]

def localH_Q : Fin 5 → ℚ := ![7, -1 / 2, -1 / 2, -4 / 5, -5 / 4]

def localH_P_nonincreasing_prop : Prop :=
  ∀ i j : Fin 2, i ≤ j → localH_P j ≤ localH_P i

def localH_Q_nonincreasing_prop : Prop :=
  ∀ i j : Fin 5, i ≤ j → localH_Q j ≤ localH_Q i

theorem product_coefficients : P * Q = C := by
  simp only [P, Q, C]
  ring

theorem localH_P_nonincreasing_holds : localH_P_nonincreasing_prop := by
  unfold localH_P_nonincreasing_prop localH_P
  native_decide

theorem localH_Q_nonincreasing_holds : localH_Q_nonincreasing_prop := by
  unfold localH_Q_nonincreasing_prop localH_Q
  native_decide

theorem displayed_localH_values :
    localH_P 0 = 3 ∧ localH_P 1 = 2 ∧
      localH_Q 0 = 7 ∧ localH_Q 1 = -(1 / 2 : ℚ) ∧
      localH_Q 2 = -(1 / 2 : ℚ) ∧
      localH_Q 3 = -(4 / 5 : ℚ) ∧
      localH_Q 4 = -(5 / 4 : ℚ) := by
  native_decide

/-- The exact finite product and displayed `h₃ < h₄` countercertificate. -/
theorem componentwiseOrderedGSB_failure_claim46855 :
    P * Q = C ∧
      localH_P_nonincreasing_prop ∧
      localH_Q_nonincreasing_prop ∧
      localH_P 0 = 3 ∧ localH_P 1 = 2 ∧
      localH_Q 0 = 7 ∧ localH_Q 1 = -(1 / 2 : ℚ) ∧
      localH_Q 2 = -(1 / 2 : ℚ) ∧
      localH_Q 3 = -(4 / 5 : ℚ) ∧
      localH_Q 4 = -(5 / 4 : ℚ) ∧
      (-28 : ℚ) / 31 < (-65 : ℚ) / 72 := by
  refine ⟨product_coefficients, localH_P_nonincreasing_holds,
    localH_Q_nonincreasing_holds, displayed_localH_values.1,
    displayed_localH_values.2.1, displayed_localH_values.2.2.1,
    displayed_localH_values.2.2.2.1,
    displayed_localH_values.2.2.2.2.1,
    displayed_localH_values.2.2.2.2.2.1,
    displayed_localH_values.2.2.2.2.2.2, by norm_num⟩

end MathlibPlus.Combinatorics.Claim46855
